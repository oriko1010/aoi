use crate::{ast, parser::Parser, AoiOptions};
use anyhow::{anyhow, bail, ensure, Result};
use inkwell::{
    builder::Builder,
    context::Context,
    execution_engine::{ExecutionEngine, JitFunction},
    module::{Linkage, Module},
    passes::PassManager,
    types::{self, BasicType, BasicTypeEnum, FloatType, FunctionType, IntType},
    values::{
        AnyValue, AnyValueEnum, BasicValue, BasicValueEnum, FloatValue, FunctionValue, IntValue,
        PointerValue, UnnamedAddress,
    },
    AddressSpace, FloatPredicate, IntPredicate, OptimizationLevel,
};
use std::collections::HashMap;
use types::{AnyType, AnyTypeEnum, PointerType, StructType};

pub fn compile(program: ast::Program, opts: &AoiOptions) -> Result<i32> {
    let context = Context::create();
    let builder = context.create_builder();
    let module = context.create_module("Aoi");
    let fpm = PassManager::create(&module);
    if opts.optimize {
        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();
        fpm.add_gvn_pass();
        fpm.add_cfg_simplification_pass();
        fpm.add_promote_memory_to_register_pass();
        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();
    }
    if !opts.no_verify {
        fpm.add_verifier_pass();
    }
    fpm.initialize();
    let execution_engine = module
        .create_jit_execution_engine(OptimizationLevel::None)
        .map_err(|e| anyhow!("{}", e))?;
    let aoi = AoiContext::new(&context);
    let scopes = Vec::with_capacity(8);

    let mut codegen = Codegen {
        optimize: opts.optimize,
        print: opts.show,
        verify: !opts.no_verify,
        context: &context,
        builder,
        module,
        fpm,
        execution_engine,
        aoi,
        scopes,
    };

    if opts.libc {
        let code = std::fs::read_to_string("./bindings/libc.aoi")?;
        let libc = Parser::new(&code).parse_program()?;
        codegen.compile(libc)?;
    }

    codegen.compile(program)?;

    let main = codegen.jit("main")?;
    let result = unsafe { main.call() };
    Ok(result)
}

pub struct Codegen<'a> {
    optimize: bool,
    print: bool,
    verify: bool,
    context: &'a Context,
    builder: Builder<'a>,
    module: Module<'a>,
    fpm: PassManager<FunctionValue<'a>>,
    execution_engine: ExecutionEngine<'a>,
    aoi: AoiContext<'a>,
    scopes: Vec<Scope<'a>>,
}

const CALL_CONV: u32 = 8;

impl<'a> Codegen<'a> {
    pub fn compile(&mut self, program: ast::Program) -> Result<()> {
        for expression in program.expressions {
            self.compile_expresion(expression, None)?;
        }

        if self.print {
            self.module.print_to_stderr();
        }

        Ok(())
    }

    fn jit(&self, name: &str) -> Result<JitFunction<unsafe extern "C" fn() -> i32>> {
        unsafe {
            self.execution_engine
                .get_function(name)
                .map_err(|_| anyhow!("Error jitting function {}", name))
        }
    }

    fn compile_expresion(
        &mut self,
        expression: ast::Expression,
        target_type: Option<Type<'a>>,
    ) -> Result<Value<'a>> {
        match expression {
            ast::Expression::If(if_ast) => self.compile_if(if_ast, target_type),
            ast::Expression::For(for_ast) => self.compile_for(for_ast, target_type),
            ast::Expression::Assign(assign) => self.compile_assign(assign),
            ast::Expression::TypeDefinition(ty) => self.compile_type_definition(ty),
            ast::Expression::Function(function) => self.compile_function(function),
            ast::Expression::Call(call) => self.compile_call(call),
            ast::Expression::Block(block) => self.compile_block(block),
            ast::Expression::UnaryOp(unary_op) => self.compile_unary_op(unary_op),
            ast::Expression::BinaryOp(binary_op) => self.compile_binary_op(binary_op),
            ast::Expression::Integer(integer) => self.compile_integer(
                integer,
                target_type.unwrap_or_else(|| self.aoi.type_from_kind(TypeKind::Int(32)).unwrap()),
            ),
            ast::Expression::Float(float) => self.compile_float(
                float,
                target_type.unwrap_or_else(|| self.aoi.type_from_kind(TypeKind::F64).unwrap()),
            ),
            ast::Expression::Bool(boolean) => self.compile_bool(boolean),
            ast::Expression::String(string) => self.compile_string(string),
            ast::Expression::Identifier(identifier) => self.compile_identifier(identifier),
            _ => bail!("Unknown expression: {:?}", expression),
        }
    }

    fn compile_type_definition(&mut self, def: ast::TypeDefinition) -> Result<Value<'a>> {
        let ast::TypeDefinition { identifier, value } = def.clone();

        match value {
            ast::TypeBody::Extern => {
                let opaque = self.context.opaque_struct_type(&*identifier.name);
                self.aoi
                    .add_type(TypeKind::Extern(def.identifier), opaque.into())?;
                Ok(self.aoi.unit_value())
            }
            ast::TypeBody::Alias(alias) => {
                let kind = self
                    .aoi
                    .type_kind_from_ast(&alias)
                    .ok_or_else(|| anyhow!("Could not resolve type alias: {:?}", alias))?;

                let ty = self
                    .aoi
                    .type_from_kind(kind.clone())
                    .ok_or_else(|| anyhow!("Could not resolve llvm type alias: {:?}", kind))?;

                self.aoi
                    .add_type(TypeKind::Alias(def.identifier, box kind), ty.llvm_type)?;
                Ok(self.aoi.unit_value())
            }
        }
    }

    fn compile_function(&mut self, function: ast::Function) -> Result<Value<'a>> {
        let ast::Function { signature, body } = function;

        let function = self.declare_function(signature.clone())?;

        let body = match body {
            ast::FunctionBody::Extern => return Ok(self.aoi.unit_value()),
            ast::FunctionBody::Body(body) => body,
        };

        let block = self.context.append_basic_block(function, "body");
        
        self.enter_scope();

        let mut arg_names = Vec::with_capacity(signature.arguments.len());
        let mut arg_types = Vec::with_capacity(signature.arguments.len());
        for (arg_name, arg_type) in &signature.arguments {
            arg_names.push(arg_name);
            arg_types.push(
                self.aoi
                    .type_from_ast(arg_type)
                    .ok_or_else(|| anyhow!("Could not resolve argument type: {:?}", arg_type))?,
            );
        }

        for (i, argument) in function.get_param_iter().enumerate() {
            let alloca = self.create_alloca(function, &arg_names[i].name, arg_types[i].clone())?;
            self.current_scope().unwrap().insert(
                &*arg_names[i].name,
                arg_types[i].clone().value(alloca.into()),
            );

            self.builder.position_at_end(block);
            self.builder
                .build_store(alloca, argument.as_basic_value_enum());
        }

        self.builder.position_at_end(block);
        let return_type = self
            .aoi
            .type_from_ast(&signature.return_type)
            .ok_or_else(|| anyhow!("Could not resolve return type: {:?}", signature.return_type))?;

        let value = self.compile_expresion(*body, Some(return_type.clone()))?;
        match return_type.kind {
            TypeKind::Unit => self.builder.build_return(None),
            _ => match value.llvm_value {
                LlvmValueWrapper::Basic(basic) => self.builder.build_return(Some(&basic)),
                _ => bail!(
                    "Could not return non basic llvm value: {:?}",
                    value.llvm_value
                ),
            },
        };

        self.exit_scope()?;

        if self.verify {
            function.verify(true);
        }
        self.fpm.run_on(&function);

        Ok(value)
    }

    fn compile_call(&mut self, call: ast::Call) -> Result<Value<'a>> {
        let ast::Call {
            identifier,
            arguments,
        } = call;

        let (args, signature) = match self.aoi.find_functions(&identifier.name, arguments.len()) {
            SignatureMatch::None => bail!("No function signature {} found", identifier.name),
            SignatureMatch::Single(signature) => {
                let signature = signature.clone();
                let mut args = Vec::with_capacity(arguments.len());
                for (i, argument) in arguments.into_iter().enumerate() {
                    let target_type = &signature.arguments[i].1;
                    let target_type = self
                        .aoi
                        .type_from_ast(target_type)
                        .ok_or_else(|| anyhow!("Could not resolve type {:?}", target_type))?
                        .clone();
                    let arg = self.compile_expresion(argument, Some(target_type))?;
                    args.push(arg.llvm_value.basic()?);
                }
                (args, signature)
            }
            SignatureMatch::Multiple(multiple) => {
                let mut args = Vec::with_capacity(arguments.len());
                let mut candidates = Vec::new();
                for signature in multiple.clone() {
                    let mut arg_types = Vec::new();
                    for i in 0..arguments.len() {
                        let arg_type = self.aoi.type_from_ast(&signature.arguments[i].1).unwrap();
                        arg_types.push(arg_type);
                    }
                    candidates.push((arg_types, signature.clone()));
                }

                for (i, argument) in arguments.into_iter().enumerate() {
                    match candidates.len() {
                        0 => bail!("No overload candidates found"),
                        1 => {
                            let arg =
                                self.compile_expresion(argument, Some(candidates[0].0[i].clone()))?;
                            args.push(arg.llvm_value.basic()?);
                        }
                        _ => {
                            let arg = self.compile_expresion(argument, None)?;
                            candidates.retain(|(types, _)| types[i].kind == arg.ty.kind);
                            args.push(arg.llvm_value.basic()?);
                        }
                    };
                }

                match candidates.len() {
                    0 => bail!("No overload candidates found"),
                    1 => (args, candidates[0].1.clone()),
                    _ => bail!("Multiple overloads found: {:?}", candidates),
                }
            }
        };

        let return_type = self
            .aoi
            .type_from_ast(&signature.return_type)
            .ok_or_else(|| anyhow!("Could not resolve return type {:?}", signature.return_type))?;

        let function = self.aoi.value_of(&signature)?;

        let call = self.builder.build_call(function, &args, "call");
        if signature.identifier != "main" && !signature.is_extern {
            call.set_call_convention(CALL_CONV);
        }

        if let Some(call) = call.try_as_basic_value().left() {
            Ok(return_type.value(call.into()))
        } else {
            Ok(Type::new(
                TypeKind::Unit,
                self.context.void_type().as_any_type_enum().into(),
            )
            .value(LlvmValueWrapper::UNIT))
        }
    }

    fn compile_assign(&mut self, assign: ast::Assign) -> Result<Value<'a>> {
        let ast::Assign {
            identifier: ast::Identifier { name },
            expression,
        } = assign;

        let value = self.compile_expresion(*expression, None)?;

        let function = self.current_function()?;
        let alloca = self.create_alloca(function, &*name, value.ty.clone())?;
        self.current_scope()
            .unwrap()
            .insert(&*name, value.ty.clone().value(alloca.into()));

        self.builder.position_at_end(
            function
                .get_last_basic_block()
                .ok_or_else(|| anyhow!("No basic blocks"))?,
        );

        match value.llvm_value {
            LlvmValueWrapper::Basic(basic) => self.builder.build_store(alloca, basic),
            _ => {
                return Err(anyhow!(
                    "Could not store non basic llvm value {:?}",
                    value.llvm_value
                ))
            }
        };

        Ok(value)
    }

    fn compile_block(&mut self, block: ast::Block) -> Result<Value<'a>> {
        let ast::Block { expressions } = block;

        self.enter_scope();
        let mut last_value = None;
        for expression in expressions {
            last_value = Some(self.compile_expresion(expression, None)?);
        }
        self.exit_scope()?;

        last_value.ok_or_else(|| anyhow!("Empty block"))
    }

    fn compile_if(&mut self, if_ast: ast::If, target_type: Option<Type<'a>>) -> Result<Value<'a>> {
        let ast::If {
            condition,
            then,
            other,
        } = if_ast;

        let function = self
            .builder
            .get_insert_block()
            .and_then(|block| block.get_parent())
            .ok_or_else(|| anyhow!("Could not find function when compiling if"))?;

        let other = other.ok_or_else(|| anyhow!("If expressions without else not yet allowed"))?;

        let condition =
            self.compile_expresion(*condition, self.aoi.type_from_kind(TypeKind::Bool))?;
        let condition = match condition {
            Value {
                llvm_value: LlvmValueWrapper::Basic(basic),
                ..
            } => basic.into_int_value(),
            _ => return Err(anyhow!("Error compiling if expression")),
        };

        let comparison = self.builder.build_int_compare(
            inkwell::IntPredicate::NE,
            condition,
            self.context.bool_type().const_zero(),
            "if",
        );

        let then_block = self.context.append_basic_block(function, "then");
        let else_block = self.context.append_basic_block(function, "else");
        let merge_block = self.context.append_basic_block(function, "merge");

        self.builder
            .build_conditional_branch(comparison, then_block, else_block);

        self.builder.position_at_end(then_block);
        let then_value = self.compile_expresion(*then, target_type.clone())?;
        self.builder.build_unconditional_branch(merge_block);
        let then_block = self.builder.get_insert_block().unwrap();

        self.builder.position_at_end(else_block);
        let else_value = self.compile_expresion(*other, target_type.clone())?;
        self.builder.build_unconditional_branch(merge_block);
        let else_block = self.builder.get_insert_block().unwrap();

        self.builder.position_at_end(merge_block);

        let phi_type = match target_type {
            None => then_value.ty,
            Some(ty) if ty.kind == TypeKind::Unit => return Ok(self.aoi.unit_value()),
            Some(ty) => ty,
        };

        let phi = self
            .builder
            .build_phi(phi_type.clone().llvm_type.basic()?, "ifvalue");
        phi.add_incoming(&[
            (&then_value.llvm_value.basic()?, then_block),
            (&else_value.llvm_value.basic()?, else_block),
        ]);
        Ok(phi_type.value(phi.as_basic_value().into()))
    }

    fn compile_for(
        &mut self,
        for_ast: ast::For,
        target_type: Option<Type<'a>>,
    ) -> Result<Value<'a>> {
        let ast::For {
            init,
            condition,
            iteration,
            body,
        } = for_ast;

        self.compile_expresion(*init, None)?;

        let function = self
            .builder
            .get_insert_block()
            .and_then(|block| block.get_parent())
            .ok_or_else(|| anyhow!("Could not find function when compiling for"))?;

        let cond_block = self.context.append_basic_block(function, "cond");
        let body_block = self.context.append_basic_block(function, "body");
        let done_block = self.context.append_basic_block(function, "done");

        self.builder.build_unconditional_branch(cond_block);
        self.builder.position_at_end(cond_block);

        let condition = self.compile_expresion(
            *condition,
            Some(self.aoi.type_from_kind(TypeKind::Bool).unwrap()),
        )?;

        self.builder.build_conditional_branch(
            condition.llvm_value.basic()?.into_int_value(),
            body_block,
            done_block,
        );

        self.builder.position_at_end(body_block);

        self.compile_expresion(*body, target_type)?;
        self.compile_expresion(*iteration, None)?;
        self.builder.build_unconditional_branch(cond_block);

        self.builder.position_at_end(done_block);

        Ok(self.aoi.unit_value())
    }

    fn compile_unary_op(&mut self, unary_op: ast::UnaryOp) -> Result<Value<'a>> {
        let ast::UnaryOp { op, expression } = unary_op;

        let expr = self.compile_expresion(*expression, None)?;
        let ty = expr.ty;

        if &*op == "-" {
            match expr.llvm_value.basic()? {
                BasicValueEnum::IntValue(expr) => {
                    return Ok(ty.clone().value(
                        self.builder
                            .build_int_sub(ty.llvm_type.integer()?.const_zero(), expr, "neg")
                            .into(),
                    ))
                }
                BasicValueEnum::FloatValue(expr) => {
                    return Ok(ty.value(self.builder.build_float_neg(expr, "neg").into()))
                }
                _ => {
                    return Err(anyhow!("Wrong llvm value in unary - op"));
                }
            }
        } else if &*op == "!" {
            if ty.kind == TypeKind::Bool {
                return Ok(ty.value(
                    self.builder
                        .build_not(expr.llvm_value.basic()?.into_int_value(), "not")
                        .into(),
                ));
            }
            return Err(anyhow!("Wrong llvm value in unary ! op"));
        }
        Err(anyhow!("Unknown unary op"))
    }

    fn compile_binary_op(&mut self, binary_op: ast::BinaryOp) -> Result<Value<'a>> {
        let ast::BinaryOp { lhs, op, rhs } = binary_op;

        if &*op == "=" {
            if let ast::Expression::Identifier(ast::Identifier { name }) = *lhs {
                let rhs = self.compile_expresion(*rhs, None)?;
                let value = self.value_in_scope(&*name)?;

                return match value.llvm_value {
                    LlvmValueWrapper::Basic(BasicValueEnum::PointerValue(ptr)) => {
                        self.builder.build_store(ptr, rhs.llvm_value.basic()?);
                        Ok(value
                            .ty
                            .clone()
                            .value(self.builder.build_load(ptr, &*name).into()))
                    }
                    _ => Err(anyhow!(
                        "Can't assign to a non pointer llvm value {:?}",
                        value.llvm_value
                    )),
                };
            }
        }

        let lhs = self.compile_expresion(*lhs, None)?;
        let rhs = self.compile_expresion(*rhs, None)?;

        let ty = if lhs.ty.kind == rhs.ty.kind {
            lhs.ty
        } else {
            return Err(anyhow!(
                "Binary op {} types {:?} and {:?} don't match",
                op,
                lhs.ty,
                rhs.ty
            ));
        };

        if &*op == "+" {
            match (lhs.llvm_value.basic()?, rhs.llvm_value.basic()?) {
                (BasicValueEnum::IntValue(lhs), BasicValueEnum::IntValue(rhs)) => {
                    return Ok(ty.value(self.builder.build_int_add(lhs, rhs, "add").into()));
                }
                (BasicValueEnum::FloatValue(lhs), BasicValueEnum::FloatValue(rhs)) => {
                    return Ok(ty.value(self.builder.build_float_add(lhs, rhs, "add").into()));
                }
                _ => {
                    return Err(anyhow!("Wrong llvm value in binary + op"));
                }
            }
        } else if &*op == "-" {
            match (lhs.llvm_value.basic()?, rhs.llvm_value.basic()?) {
                (BasicValueEnum::IntValue(lhs), BasicValueEnum::IntValue(rhs)) => {
                    return Ok(ty.value(self.builder.build_int_sub(lhs, rhs, "sub").into()));
                }
                (BasicValueEnum::FloatValue(lhs), BasicValueEnum::FloatValue(rhs)) => {
                    return Ok(ty.value(self.builder.build_float_sub(lhs, rhs, "sub").into()));
                }
                _ => {
                    return Err(anyhow!("Wrong llvm value in binary - op"));
                }
            }
        } else if &*op == "*" {
            match (lhs.llvm_value.basic()?, rhs.llvm_value.basic()?) {
                (BasicValueEnum::IntValue(lhs), BasicValueEnum::IntValue(rhs)) => {
                    return Ok(ty.value(self.builder.build_int_mul(lhs, rhs, "mul").into()));
                }
                (BasicValueEnum::FloatValue(lhs), BasicValueEnum::FloatValue(rhs)) => {
                    return Ok(ty.value(self.builder.build_float_mul(lhs, rhs, "mul").into()));
                }
                _ => {
                    return Err(anyhow!("Wrong llvm value in binary * op"));
                }
            }
        } else if &*op == "/" {
            match (lhs.llvm_value.basic()?, rhs.llvm_value.basic()?) {
                (BasicValueEnum::IntValue(lhs), BasicValueEnum::IntValue(rhs)) => {
                    return match ty.kind {
                        TypeKind::Int(_) => {
                            Ok(ty.value(self.builder.build_int_signed_div(lhs, rhs, "div").into()))
                        }
                        TypeKind::UInt(_) => {
                            Ok(ty
                                .value(self.builder.build_int_unsigned_div(lhs, rhs, "div").into()))
                        }
                        _ => bail!("Non int type"),
                    }
                }
                (BasicValueEnum::FloatValue(lhs), BasicValueEnum::FloatValue(rhs)) => {
                    return Ok(ty.value(self.builder.build_float_div(lhs, rhs, "div").into()));
                }
                _ => {
                    return Err(anyhow!("Wrong llvm value in binary / op"));
                }
            }
        } else if &*op == "<" {
            match (lhs.llvm_value.basic()?, rhs.llvm_value.basic()?) {
                (BasicValueEnum::IntValue(lhs), BasicValueEnum::IntValue(rhs)) => {
                    return match ty.kind {
                        TypeKind::Int(_) => Ok(ty.value(
                            self.builder
                                .build_int_compare(IntPredicate::SLT, lhs, rhs, "slt")
                                .into(),
                        )),
                        TypeKind::UInt(_) => Ok(ty.value(
                            self.builder
                                .build_int_compare(IntPredicate::ULT, lhs, rhs, "slt")
                                .into(),
                        )),
                        _ => bail!("Non int type"),
                    }
                }
                (BasicValueEnum::FloatValue(lhs), BasicValueEnum::FloatValue(rhs)) => {
                    return Ok(ty.value(
                        self.builder
                            .build_float_compare(FloatPredicate::ULT, lhs, rhs, "ult")
                            .into(),
                    ));
                }
                _ => {
                    return Err(anyhow!("Wrong llvm value in binary < op"));
                }
            }
        } else if &*op == ">" {
            match (lhs.llvm_value.basic()?, rhs.llvm_value.basic()?) {
                (BasicValueEnum::IntValue(lhs), BasicValueEnum::IntValue(rhs)) => {
                    return match ty.kind {
                        TypeKind::Int(_) => Ok(ty.value(
                            self.builder
                                .build_int_compare(IntPredicate::SGT, lhs, rhs, "sgt")
                                .into(),
                        )),
                        TypeKind::UInt(_) => Ok(ty.value(
                            self.builder
                                .build_int_compare(IntPredicate::UGT, lhs, rhs, "ugt")
                                .into(),
                        )),
                        _ => bail!("Non int type"),
                    }
                }
                (BasicValueEnum::FloatValue(lhs), BasicValueEnum::FloatValue(rhs)) => {
                    return Ok(ty.value(
                        self.builder
                            .build_float_compare(FloatPredicate::UGT, lhs, rhs, "ugt")
                            .into(),
                    ));
                }
                _ => {
                    return Err(anyhow!("Wrong llvm value in binary > op"));
                }
            }
        }

        Err(anyhow!("Unknown binary op"))
    }

    fn compile_identifier(&self, identifier: ast::Identifier) -> Result<Value<'a>> {
        let ast::Identifier { name } = identifier;

        let named_value = self.value_in_scope(&*name)?;
        let load = match named_value.llvm_value {
            LlvmValueWrapper::Basic(BasicValueEnum::PointerValue(ptr)) => {
                self.builder.build_load(ptr, &*name)
            }
            _ => bail!(
                "Tried to load from non pointer llvm value {:?}",
                named_value.llvm_value
            ),
        };
        Ok(named_value.ty.clone().value(load.into()))
    }

    fn compile_bool(&self, boolean: ast::Bool) -> Result<Value<'a>> {
        let ty = self.aoi.type_from_kind(TypeKind::Bool).unwrap();
        let llvm_value = ty
            .llvm_type
            .clone()
            .integer()?
            .const_int(if boolean.value { 1 } else { 0 }, false);
        Ok(ty.value(llvm_value.into()))
    }

    fn compile_integer(&self, integer: ast::Integer, target_type: Type<'a>) -> Result<Value<'a>> {
        match target_type.kind {
            TypeKind::F16 | TypeKind::F32 | TypeKind::F64 | TypeKind::F128 => {
                let value = target_type
                    .llvm_type
                    .clone()
                    .float()?
                    .const_float(integer.value as f64);
                Ok(target_type.value(value.into()))
            }
            TypeKind::Int(_) | TypeKind::UInt(_) => {
                let value = target_type
                    .llvm_type
                    .clone()
                    .integer()?
                    .const_int(integer.value, false);
                Ok(target_type.value(value.into()))
            }
            _ => Err(anyhow!(
                "Can't compile integer to target type {:?}",
                target_type
            )),
        }
    }

    fn compile_float(&self, float: ast::Float, target_type: Type<'a>) -> Result<Value<'a>> {
        match target_type.kind {
            TypeKind::F16 | TypeKind::F32 | TypeKind::F64 | TypeKind::F128 => {
                let value = target_type
                    .llvm_type
                    .clone()
                    .float()?
                    .const_float(float.value);
                Ok(target_type.value(value.into()))
            }
            _ => Err(anyhow!(
                "Can't compile float to target type {:?}",
                target_type
            )),
        }
    }

    fn compile_string(&self, string: ast::String) -> Result<Value<'a>> {
        let value = self.context.const_string(string.value.as_bytes(), true);
        let global = self.module.add_global(value.get_type(), None, "str");
        global.set_initializer(&value.as_basic_value_enum());
        global.set_constant(true);
        global.set_linkage(Linkage::Private);
        global.set_unnamed_address(UnnamedAddress::Global);

        let get = unsafe {
            self.builder.build_gep(
                global.as_pointer_value(),
                &[
                    self.context.i64_type().const_zero(),
                    self.context.i64_type().const_zero(),
                ],
                "get",
            )
        };

        Ok(self
            .aoi
            .type_from_kind(TypeKind::Pointer(box TypeKind::UInt(8)))
            .unwrap()
            .value(get.into()))
    }

    fn current_function(&self) -> Result<FunctionValue<'a>> {
        self.builder
            .get_insert_block()
            .and_then(|block| block.get_parent())
            .ok_or_else(|| anyhow!("Could not get current function."))
    }

    fn create_alloca(
        &self,
        function: FunctionValue<'a>,
        name: &str,
        ty: Type<'a>,
    ) -> Result<PointerValue<'a>> {
        let builder = self.context.create_builder();

        let block = function
            .get_first_basic_block()
            .ok_or_else(|| anyhow!("No basic block in function"))?;
        match block.get_first_instruction() {
            Some(first) => builder.position_before(&first),
            None => builder.position_at_end(block),
        };

        Ok(builder.build_alloca(ty.llvm_type.clone().basic()?, name))
    }

    fn declare_function(&mut self, signature: ast::FunctionSignature) -> Result<FunctionValue<'a>> {
        let return_ty = self
            .aoi
            .type_kind_from_ast(&signature.return_type)
            .ok_or_else(|| {
                anyhow!(
                    "Error resolving function return type: {:?}",
                    signature.return_type
                )
            })?;

        let mut argument_types = Vec::with_capacity(signature.arguments.len());
        let mut argument_names = Vec::with_capacity(signature.arguments.len());
        for (argument_name, argument_ty) in &signature.arguments {
            let argument_ty = self.aoi.type_kind_from_ast(argument_ty).ok_or_else(|| {
                anyhow!("Error resolving function parameter type: {:?}", argument_ty)
            })?;
            argument_names.push(argument_name);
            argument_types.push(argument_ty);
        }

        let fun_ty = self
            .aoi
            .type_from_kind(TypeKind::Function(argument_types, box return_ty))
            .ok_or_else(|| anyhow!("Error resolving function type"))?;

        let llvm_fun = self.module.add_function(
            &signature.identifier.name,
            fun_ty.llvm_type.function()?,
            Some(Linkage::External),
        );
        for (i, param) in llvm_fun.get_param_iter().enumerate() {
            match param {
                BasicValueEnum::IntValue(int) => int.set_name(&*argument_names[i].name),
                BasicValueEnum::FloatValue(float) => float.set_name(&*argument_names[i].name),
                BasicValueEnum::PointerValue(ptr) => ptr.set_name(&*argument_names[i].name),
                _ => {}
            }
        }

        if signature.identifier != "main" && !signature.is_extern {
            llvm_fun.set_call_conventions(CALL_CONV);
        }

        self.aoi.add_signature(signature, llvm_fun)?;

        Ok(llvm_fun)
    }

    fn enter_scope(&mut self) {
        let scope = Scope::new();
        self.scopes.push(scope);
    }

    fn exit_scope(&mut self) -> Result<()> {
        self.scopes
            .pop()
            .map(|_| ())
            .ok_or_else(|| anyhow!("Tried exiting a scope when there's none left."))
    }

    fn current_scope(&mut self) -> Option<&mut Scope<'a>> {
        self.scopes.last_mut()
    }

    fn value_in_scope(&self, name: &str) -> Result<&Value<'a>> {
        for scope in self.scopes.iter().rev() {
            match scope.values.get(name) {
                Some(value) => return Ok(value),
                None => continue,
            }
        }
        bail!("No value named {} found in scope", name)
    }
}

struct AoiContext<'a> {
    context: &'a Context,
    functions: Vec<ast::FunctionSignature>,
    fun_values: Vec<FunctionValue<'a>>,
    types: Vec<TypeKind>,
    ty_values: Vec<LlvmTypeWrapper<'a>>,
}

impl<'a> AoiContext<'a> {
    fn new(context: &'a Context) -> Self {
        Self {
            context,
            functions: Vec::new(),
            fun_values: Vec::new(),
            types: Vec::new(),
            ty_values: Vec::new(),
        }
    }

    fn add_type(&mut self, def: TypeKind, ty: LlvmTypeWrapper<'a>) -> Result<()> {
        ensure!(
            !self.types.contains(&def),
            "Type definition {:?} already exists.",
            def
        );
        self.types.push(def);
        self.ty_values.push(ty);
        Ok(())
    }

    fn add_signature(
        &mut self,
        signature: ast::FunctionSignature,
        value: FunctionValue<'a>,
    ) -> Result<()> {
        ensure!(
            !self.functions.contains(&signature),
            "Function definition {:?} already exists.",
            signature
        );
        self.functions.push(signature);
        self.fun_values.push(value);
        Ok(())
    }

    fn type_from_ast(&self, ty: &ast::Type) -> Option<Type<'a>> {
        let kind = self.type_kind_from_ast(ty)?;
        self.type_from_kind(kind)
    }

    fn find_functions(&self, name: &str, arguments: usize) -> SignatureMatch {
        use SignatureMatch::*;
        let mut found = None;
        for signature in self.functions.iter() {
            if signature.identifier == name && signature.arguments.len() == arguments {
                found = match found {
                    None => Single(signature),
                    Single(first) => Multiple(vec![first, signature]),
                    Multiple(mut multiple) => {
                        multiple.push(signature);
                        Multiple(multiple)
                    }
                }
            }
        }
        found
    }

    fn value_of(&self, signature: &ast::FunctionSignature) -> Result<FunctionValue<'a>> {
        let index = self
            .functions
            .iter()
            .position(|s| s == signature)
            .ok_or_else(|| anyhow!("No function signature {:?} found.", signature))?;
        Ok(self.fun_values[index])
    }

    fn unit_value(&self) -> Value<'a> {
        self.type_from_kind(TypeKind::Unit)
            .unwrap()
            .value(LlvmValueWrapper::UNIT)
    }

    fn type_from_kind(&self, kind: TypeKind) -> Option<Type<'a>> {
        use TypeKind::*;
        let context = self.context;
        match kind {
            Unit => Type::new(kind, context.void_type().as_any_type_enum().into()).into(),
            Bool => Type::new(kind, context.bool_type().into()).into(),
            F16 => Type::new(kind, context.f16_type().into()).into(),
            F32 => Type::new(kind, context.f32_type().into()).into(),
            F64 => Type::new(kind, context.f64_type().into()).into(),
            F128 => Type::new(kind, context.f128_type().into()).into(),
            Int(size) => Type::new(kind, context.custom_width_int_type(size).into()).into(),
            UInt(size) => Type::new(kind, context.custom_width_int_type(size).into()).into(),
            Pointer(to) => Type::new(
                Pointer(to.clone()),
                self.type_from_kind(*to)
                    .unwrap()
                    .llvm_type
                    .basic()
                    .unwrap()
                    .ptr_type(AddressSpace::Generic)
                    .into(),
            )
            .into(),
            Function(args, ret) => {
                let kind = Function(args.clone(), ret.clone());
                let args = args
                    .iter()
                    .map(|arg| {
                        self.type_from_kind(arg.clone())
                            .unwrap()
                            .llvm_type
                            .basic()
                            .unwrap()
                    })
                    .collect::<Vec<_>>();
                let ret = self.type_from_kind(*ret).unwrap();

                Type::new(kind, ret.llvm_type.make_function(&args).unwrap().into()).into()
            }
            other => {
                let index = self.types.iter().position(|f| *f == other)?;
                Type::new(other, self.ty_values[index].clone()).into()
            }
        }
    }

    fn type_kind_from_ast(&self, ty: &ast::Type) -> Option<TypeKind> {
        let ast::Type {
            identifier: ast::Identifier { name },
            generics,
        } = ty;
        use TypeKind::*;
        match &**name {
            "unit" => Some(Unit),
            "bool" => Some(Bool),
            "f16" => Some(F16),
            "f32" => Some(F32),
            "f64" => Some(F64),
            "f128" => Some(F128),
            "Pointer" => {
                let inner = generics.as_ref()?;
                if inner.len() != 1 {
                    None
                } else {
                    let inner = self.type_kind_from_ast(&inner[0])?;
                    Some(Pointer(box inner))
                }
            }
            integer if self.integer(integer).is_some() => self.integer(integer),
            other => {
                for ty in self.types.iter() {
                    match ty {
                        TypeKind::Extern(identifier) if identifier == &other => {
                            return Some(ty.clone())
                        }
                        TypeKind::Alias(identifier, alias) if identifier == &other => {
                            return Some(*alias.clone())
                        }
                        _ => continue,
                    }
                }
                None
            }
        }
    }

    fn integer(&self, name: &str) -> Option<TypeKind> {
        if name.starts_with('i') {
            let size = name[1..].parse::<u32>().ok()?;
            Some(TypeKind::Int(size))
        } else if name.starts_with('u') {
            let size = name[1..].parse::<u32>().ok()?;
            Some(TypeKind::UInt(size))
        } else {
            None
        }
    }
}

enum SignatureMatch<'a> {
    None,
    Single(&'a ast::FunctionSignature),
    Multiple(Vec<&'a ast::FunctionSignature>),
}

#[derive(Debug)]
struct Scope<'a> {
    values: HashMap<String, Value<'a>>,
}

impl<'a> Scope<'a> {
    fn new() -> Self {
        Self {
            values: HashMap::new(),
        }
    }

    fn insert(&mut self, name: &str, value: Value<'a>) {
        self.values.insert(name.to_owned(), value);
    }
}

#[derive(Clone, Debug)]
pub enum TypeKind {
    Unit,
    Bool,
    F16,
    F32,
    F64,
    F128,
    Int(u32),
    UInt(u32),
    Pointer(Box<TypeKind>),
    Slice(Box<TypeKind>),
    Function(Vec<TypeKind>, Box<TypeKind>),
    Extern(ast::Identifier),
    Alias(ast::Identifier, Box<TypeKind>),
}

impl PartialEq for TypeKind {
    fn eq(&self, other: &TypeKind) -> bool {
        use TypeKind::*;
        match (self, other) {
            (Unit, Unit) => true,
            (Bool, Bool) => true,
            (F16, F16) => true,
            (F32, F32) => true,
            (F64, F64) => true,
            (F128, F128) => true,
            (Int(x), Int(y)) => x == y,
            (UInt(x), UInt(y)) => x == y,
            (Pointer(x), Pointer(y)) => x == y,
            (Slice(x), Slice(y)) => x == y,
            (Function(x, a), Function(y, b)) => a == b && x == y,
            (Extern(x), Extern(y)) => x == y,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Type<'a> {
    kind: TypeKind,
    llvm_type: LlvmTypeWrapper<'a>,
}

impl<'a> Type<'a> {
    fn new(kind: TypeKind, llvm_type: LlvmTypeWrapper<'a>) -> Self {
        Self { kind, llvm_type }
    }

    fn value(self, llvm_value: LlvmValueWrapper<'a>) -> Value<'a> {
        Value::new(self, llvm_value)
    }
}

#[derive(Debug)]
pub struct Value<'a> {
    ty: Type<'a>,
    llvm_value: LlvmValueWrapper<'a>,
}

impl<'a> Value<'a> {
    fn new(ty: Type<'a>, llvm_value: LlvmValueWrapper<'a>) -> Self {
        Self { ty, llvm_value }
    }
}

#[derive(Debug)]
enum LlvmValueWrapper<'a> {
    Basic(BasicValueEnum<'a>),
    Any(Option<AnyValueEnum<'a>>),
}

impl<'a> LlvmValueWrapper<'a> {
    const UNIT: Self = Self::Any(None);

    fn basic(self) -> Result<BasicValueEnum<'a>> {
        match self {
            LlvmValueWrapper::Basic(basic) => Ok(basic),
            _ => Err(anyhow!("Error getting basic llvm value")),
        }
    }

    fn any(self) -> Result<AnyValueEnum<'a>> {
        match self {
            LlvmValueWrapper::Any(Some(any)) => Ok(any),
            LlvmValueWrapper::Any(None) => Err(anyhow!("Error getting any llvm value")),
            _ => Err(anyhow!("Error getting any llvm value")),
        }
    }
}

#[derive(Clone, Debug)]
enum LlvmTypeWrapper<'a> {
    Basic(BasicTypeEnum<'a>),
    Any(AnyTypeEnum<'a>),
}

impl<'a> LlvmTypeWrapper<'a> {
    fn basic(self) -> Result<BasicTypeEnum<'a>> {
        match self {
            LlvmTypeWrapper::Basic(basic) => Ok(basic),
            _ => Err(anyhow!("Error getting basic llvm type")),
        }
    }

    fn any(self) -> Result<AnyTypeEnum<'a>> {
        match self {
            LlvmTypeWrapper::Any(any) => Ok(any),
            _ => Err(anyhow!("Error getting any llvm type")),
        }
    }

    fn integer(self) -> Result<IntType<'a>> {
        match self {
            LlvmTypeWrapper::Basic(BasicTypeEnum::IntType(int)) => Ok(int),
            LlvmTypeWrapper::Any(AnyTypeEnum::IntType(int)) => Ok(int),
            _ => Err(anyhow!("Error getting float llvm type")),
        }
    }

    fn float(self) -> Result<FloatType<'a>> {
        match self {
            LlvmTypeWrapper::Basic(BasicTypeEnum::FloatType(float)) => Ok(float),
            LlvmTypeWrapper::Any(AnyTypeEnum::FloatType(float)) => Ok(float),
            _ => Err(anyhow!("Error getting float llvm type")),
        }
    }

    fn function(self) -> Result<FunctionType<'a>> {
        match self {
            LlvmTypeWrapper::Any(AnyTypeEnum::FunctionType(function)) => Ok(function),
            _ => Err(anyhow!("Error getting function llvm type")),
        }
    }

    fn make_function(self, arguments: &[BasicTypeEnum<'a>]) -> Result<FunctionType<'a>> {
        match self {
            LlvmTypeWrapper::Any(AnyTypeEnum::VoidType(void)) => Ok(void.fn_type(arguments, false)),
            LlvmTypeWrapper::Basic(basic) => Ok(basic.fn_type(arguments, false)),
            _ => Err(anyhow!("Error getting function llvm type")),
        }
    }
}

macro_rules! wrapper_from {
    ( for $wrapper:ty { $( $arg:ident: $from:ty => $which:ident($val:expr) ),* $(,)? } ) => {
        $(
            impl<'a> From<$from> for $wrapper {
                #[inline]
                fn from($arg: $from) -> Self {
                    Self::$which($val)
                }
            }
        )*
    };
}

wrapper_from! { for LlvmValueWrapper<'a> {
    int: IntValue<'a> => Basic(int.as_basic_value_enum()),
    float: FloatValue<'a> => Basic(float.as_basic_value_enum()),
    pointer: PointerValue<'a> => Basic(pointer.as_basic_value_enum()),
    function: FunctionValue<'a> => Any(Some(function.as_any_value_enum())),
    basic: BasicValueEnum<'a> => Basic(basic),
}}

wrapper_from! { for LlvmTypeWrapper<'a> {
    int: IntType<'a> => Basic(int.as_basic_type_enum()),
    float: FloatType<'a> => Basic(float.as_basic_type_enum()),
    pointer: PointerType<'a> => Basic(pointer.as_basic_type_enum()),
    structure: StructType<'a> => Basic(structure.as_basic_type_enum()),
    function: FunctionType<'a> => Any(function.as_any_type_enum()),
    basic: BasicTypeEnum<'a> => Basic(basic),
    any: AnyTypeEnum<'a> => Any(any),
}}
