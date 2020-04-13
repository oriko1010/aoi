use crate::ast;
use anyhow::{anyhow, bail, Result};
use inkwell::{
    builder::Builder,
    context::Context,
    execution_engine::{ExecutionEngine, JitFunction},
    module::{Linkage, Module},
    passes::PassManager,
    types::{BasicType, BasicTypeEnum, FloatType, FunctionType, IntType},
    values::{
        AnyValue, AnyValueEnum, BasicValue, BasicValueEnum, FloatValue, FunctionValue, IntValue,
        PointerValue,
    },
    AddressSpace, OptimizationLevel,
};
use std::{cell::RefCell, collections::HashMap};

pub struct Codegen<'a> {
    optimize: bool,
    context: &'a Context,
    builder: Builder<'a>,
    module: Module<'a>,
    fpm: PassManager<FunctionValue<'a>>,
    execution_engine: ExecutionEngine<'a>,
    aoi: RefCell<AoiContext<'a>>,
    type_check: RefCell<TypeCheck>,
    named_values: RefCell<HashMap<String, Value<'a>>>,
}

impl<'a> Codegen<'a> {
    pub fn new(context: &'a Context, optimize: bool) -> Self {
        let builder = context.create_builder();
        let module = context.create_module("Aoi");
        let fpm = PassManager::create(&module);
        if optimize {
            fpm.add_instruction_combining_pass();
            fpm.add_reassociate_pass();
            fpm.add_gvn_pass();
            fpm.add_cfg_simplification_pass();
            fpm.add_promote_memory_to_register_pass();
            fpm.add_instruction_combining_pass();
            fpm.add_reassociate_pass();
        }
        fpm.add_verifier_pass();
        fpm.initialize();
        let execution_engine = module
            .create_jit_execution_engine(OptimizationLevel::None)
            .unwrap();
        let aoi = RefCell::new(AoiContext::new());
        let type_check = RefCell::new(TypeCheck::new());
        let named_values = RefCell::new(HashMap::with_capacity(8));

        Self {
            optimize,
            context,
            builder,
            module,
            fpm,
            execution_engine,
            aoi,
            type_check,
            named_values,
        }
    }

    pub fn compile(&self, program: ast::Program) -> Result<()> {
        self.define_stdlib()?;

        for expression in program.expressions {
            self.compile_expresion(expression, None)?;
        }

        self.module.print_to_stderr();
        let compiled = self.jit("main")?;
        println!("main exited with {}", unsafe { compiled.call() });

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
        &self,
        expression: ast::Expression,
        target_type: Option<Type>,
    ) -> Result<Value> {
        match expression {
            ast::Expression::If(if_ast) => self.compile_if(if_ast, target_type),
            ast::Expression::Assign(assign) => self.compile_assign(assign),
            ast::Expression::Function(function) => self.compile_function(function),
            ast::Expression::Call(call) => self.compile_call(call),
            ast::Expression::Block(block) => self.compile_block(block),
            ast::Expression::BinaryOp(binary_op) => self.compile_binary_op(binary_op),
            ast::Expression::Integer(integer) => {
                self.compile_integer(integer, target_type.unwrap_or(Type::Int(32)))
            }
            ast::Expression::Bool(boolean) => self.compile_bool(boolean),
            ast::Expression::String(string) => self.compile_string(string),
            ast::Expression::Identifier(identifier) => self.compile_identifier(identifier),
            _ => bail!("Unknown expression: {:?}", expression),
        }
    }

    fn compile_function(&self, function: ast::Function) -> Result<Value> {
        let ast::Function { signature, body } = function;

        let function = self.declare_function(signature.clone())?;

        let body = match body {
            ast::FunctionBody::Extern => {
                return Ok(Type::Int(32).value(self.context.i32_type().const_zero().into()))
            }
            ast::FunctionBody::Body(body) => body,
        };

        let type_check = self.type_check.borrow();

        let block = self.context.append_basic_block(function, "body");
        {
            let mut named_values = self.named_values.borrow_mut();
            named_values.clear();

            let mut arg_names = Vec::with_capacity(signature.arguments.len());
            let mut arg_types = Vec::with_capacity(signature.arguments.len());
            for (arg_name, arg_type) in &signature.arguments {
                arg_names.push(arg_name);
                arg_types.push(
                    type_check
                        .resolve(&arg_type)
                        .ok_or(anyhow!("Could not resolve argument type: {:?}", arg_type))?,
                );
            }

            for (i, argument) in function.get_param_iter().enumerate() {
                let alloca = self.create_alloca(function, &arg_names[i].name, &arg_types[i])?;
                named_values.insert(
                    (&*arg_names[i].name).to_string(),
                    arg_types[i].clone().value(alloca.into()),
                );

                self.builder.position_at_end(block);
                self.builder
                    .build_store(alloca, argument.as_basic_value_enum());
            }
        }

        self.builder.position_at_end(block);
        let return_type = type_check.resolve(&signature.return_type).ok_or(anyhow!(
            "Could not resolve return type: {:?}",
            signature.return_type
        ))?;
        drop(type_check);

        let value = self.compile_expresion(*body, Some(return_type.clone()))?;
        match return_type {
            Type::Unit => self.builder.build_return(None),
            _ => match value.llvm_value {
                LlvmValueWrapper::Basic(basic) => self.builder.build_return(Some(&basic)),
                _ => bail!(
                    "Could not return non basic llvm value: {:?}",
                    value.llvm_value
                ),
            },
        };

        //function.verify(true);
        //self.fpm.run_on(&function);

        Ok(value)
    }

    fn compile_call(&self, call: ast::Call) -> Result<Value> {
        let ast::Call {
            identifier,
            arguments,
        } = call;
        let function = self
            .module
            .get_function(&identifier.name)
            .ok_or(anyhow!("No function {} found", identifier.name))?;

        let aoi = self.aoi.borrow();
        let signature = aoi
            .signature_of(&identifier.name)
            .ok_or(anyhow!("No function signature {} found", identifier.name))?;

        let type_check = self.type_check.borrow();

        let mut args = Vec::with_capacity(arguments.len());
        for (i, argument) in arguments.into_iter().enumerate() {
            let target_type = &signature.arguments[i].1;
            let target_type = type_check
                .resolve(target_type)
                .ok_or(anyhow!("Could not resolve type {:?}", target_type))?;
            let arg = self.compile_expresion(argument, Some(target_type))?;
            args.push(arg.llvm_value.basic()?);
        }

        let return_type = type_check.resolve(&signature.return_type).ok_or(anyhow!(
            "Could not resolve return type {:?}",
            signature.return_type
        ))?;
        drop(aoi);

        let return_value = self.builder.build_call(function, &args, "call");
        if let Some(return_value) = return_value.try_as_basic_value().left() {
            Ok(return_type.value(return_value.into()))
        } else {
            Ok(Type::Unit.value(self.context.i32_type().const_zero().into()))
        }
    }

    fn compile_assign(&self, assign: ast::Assign) -> Result<Value> {
        let ast::Assign {
            identifier: ast::Identifier { name },
            expression,
        } = assign;

        let value = self.compile_expresion(*expression, None)?;

        let function = self.current_function()?;
        let alloca = self.create_alloca(function, &*name, &value.ty)?;
        self.named_values
            .borrow_mut()
            .insert((&*name).to_string(), value.ty.clone().value(alloca.into()));

        self.builder.position_at_end(
            function
                .get_last_basic_block()
                .ok_or(anyhow!("No basic blocks"))?,
        );

        match value.llvm_value {
            LlvmValueWrapper::Basic(basic) => self.builder.build_store(alloca, basic),
            _ => Err(anyhow!(
                "Could not store non basic llvm value {:?}",
                value.llvm_value
            ))?,
        };

        Ok(value)
    }

    fn compile_block(&self, block: ast::Block) -> Result<Value> {
        let ast::Block { expressions } = block;
        let mut last_value = None;
        for expression in expressions {
            last_value = Some(self.compile_expresion(expression, None)?);
        }
        last_value.ok_or(anyhow!("Empty block"))
    }

    fn compile_if(&self, if_ast: ast::If, target_type: Option<Type>) -> Result<Value> {
        let ast::If {
            condition,
            then,
            other,
        } = if_ast;

        let function = self
            .builder
            .get_insert_block()
            .and_then(|block| block.get_parent())
            .ok_or(anyhow!("Could not find function when compiling if"))?;

        let other = other.ok_or(anyhow!("If expressions without else not yet allowed"))?;

        let condition = self.compile_expresion(*condition, Some(Type::Bool))?;
        let condition = match condition {
            Value {
                ty: Type::Bool,
                llvm_value: LlvmValueWrapper::Basic(basic),
            } => basic.into_int_value(),
            _ => Err(anyhow!("Error compiling if expression"))?,
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
            Some(ty) => ty.map_to_llvm_basic(self.context)?,
            None => self.context.i32_type().as_basic_type_enum(),
        };

        let phi = self.builder.build_phi(phi_type, "ifvalue");
        phi.add_incoming(&[
            (&then_value.llvm_value.basic()?, then_block),
            (&else_value.llvm_value.basic()?, else_block),
        ]);
        Ok(then_value.ty.value(phi.as_basic_value().into()))
    }

    fn compile_binary_op(&self, binary_op: ast::BinaryOp) -> Result<Value> {
        let ast::BinaryOp { lhs, op, rhs } = binary_op;

        if &*op == "=" {
            if let ast::Expression::Identifier(ast::Identifier { name }) = *lhs {
                let rhs = self.compile_expresion(*rhs, None)?;
                let named_values = self.named_values.borrow_mut();
                let value = {
                    named_values
                        .get(&*name)
                        .ok_or(anyhow!("No variable named {} found", name))?
                };
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

        let ty = if lhs.ty.is_same(&rhs.ty) {
            lhs.ty
        } else {
            Err(anyhow!(
                "Binary op {} types {:?} and {:?} don't match",
                op,
                lhs.ty,
                rhs.ty
            ))?
        };

        if &*op == "+" {
            match (lhs.llvm_value.basic()?, rhs.llvm_value.basic()?) {
                (BasicValueEnum::IntValue(lhs), BasicValueEnum::IntValue(rhs)) => {
                    return Ok(ty.value(self.builder.build_int_add(lhs, rhs, "add").into()));
                }
                _ => {
                    Err(anyhow!("Wrong llvm value in binary + op"))?;
                }
            }
        } else if &*op == "-" {
            match (lhs.llvm_value.basic()?, rhs.llvm_value.basic()?) {
                (BasicValueEnum::IntValue(lhs), BasicValueEnum::IntValue(rhs)) => {
                    return Ok(ty.value(self.builder.build_int_sub(lhs, rhs, "sub").into()));
                }
                _ => {
                    Err(anyhow!("Wrong llvm value in binary - op"))?;
                }
            }
        } else if &*op == "*" {
            match (lhs.llvm_value.basic()?, rhs.llvm_value.basic()?) {
                (BasicValueEnum::IntValue(lhs), BasicValueEnum::IntValue(rhs)) => {
                    return Ok(ty.value(self.builder.build_int_mul(lhs, rhs, "mul").into()));
                }
                _ => {
                    Err(anyhow!("Wrong llvm value in binary * op"))?;
                }
            }
        } else if &*op == "/" {
            match (lhs.llvm_value.basic()?, rhs.llvm_value.basic()?) {
                (BasicValueEnum::IntValue(lhs), BasicValueEnum::IntValue(rhs)) => {
                    return Ok(ty.value(self.builder.build_int_signed_div(lhs, rhs, "div").into()));
                }
                _ => {
                    Err(anyhow!("Wrong llvm value in binary / op"))?;
                }
            }
        }
        Err(anyhow!("Unknown binary op"))
    }

    fn compile_identifier(&self, identifier: ast::Identifier) -> Result<Value> {
        let ast::Identifier { name } = identifier;
        let named_values = self.named_values.borrow();

        if let Some(named_value) = named_values.get(&*name) {
            let load = match named_value.llvm_value {
                LlvmValueWrapper::Basic(BasicValueEnum::PointerValue(ptr)) => {
                    self.builder.build_load(ptr, &*name)
                }
                _ => Err(anyhow!(
                    "Tried to load from non pointer llvm value {:?}",
                    named_value.llvm_value
                ))?,
            };
            Ok(named_value.ty.clone().value(load.into()))
        } else {
            Err(anyhow!("No named value {} found", name))
        }
    }

    fn compile_bool(&self, boolean: ast::Bool) -> Result<Value> {
        let ty = Type::Bool;
        let llvm_ty = ty.map_to_boolean(self.context)?;
        let llvm_value = llvm_ty.const_int(if boolean.value { 1 } else { 0 }, false);
        Ok(Type::Bool.value(llvm_value.into()))
    }

    fn compile_integer(&self, integer: ast::Integer, target_type: Type) -> Result<Value> {
        match target_type {
            Type::F16 | Type::F32 | Type::F64 | Type::F128 => {
                let ty = target_type.map_to_float(self.context)?;
                let value = ty.const_float(integer.value as f64);
                Ok(target_type.value(value.into()))
            }
            Type::Int(_) | Type::UInt(_) => {
                let ty = target_type.map_to_integer(self.context)?;
                let value = ty.const_int(integer.value, false);
                Ok(target_type.value(value.into()))
            }
            _ => Err(anyhow!(
                "Can't compile integer to target type {:?}",
                target_type
            )),
        }
    }

    fn compile_string(&self, string: ast::String) -> Result<Value> {
        let value = self.context.const_string(string.value.as_bytes(), true);
        let global =
            self.module
                .add_global(value.get_type(), Some(AddressSpace::Const), "str");
        global.set_initializer(&value.as_basic_value_enum());
        let alloca = self.create_alloca(
            self.current_function()?,
            "temp",
            &Type::Pointer(box Type::UInt(8)),
        )?;
        self.builder.build_store(alloca, global);
        let load = self.builder.build_load(alloca, "load");

        Ok(Value::new(Type::Pointer(box Type::UInt(8)), load.into()))
    }

    fn current_function(&self) -> Result<FunctionValue> {
        self.builder
            .get_insert_block()
            .and_then(|block| block.get_parent())
            .ok_or(anyhow!("Could not get current function."))
    }

    fn create_alloca(
        &self,
        function: FunctionValue,
        name: &str,
        ty: &Type,
    ) -> Result<PointerValue<'a>> {
        let builder = self.context.create_builder();

        let block = function
            .get_first_basic_block()
            .ok_or(anyhow!("No basic block in function"))?;
        match block.get_first_instruction() {
            Some(first) => builder.position_before(&first),
            None => builder.position_at_end(block),
        };

        let ty = ty.map_to_llvm_basic(self.context)?;
        Ok(builder.build_alloca(ty, name))
    }

    fn define_stdlib(&self) -> Result<()> {
        let slice = self.context.struct_type(
            &[
                self.context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .as_basic_type_enum(),
                self.context.i64_type().as_basic_type_enum(),
            ],
            false,
        );

        let printf_ty = self.context.i32_type().fn_type(
            &[self
                .context
                .i8_type()
                .ptr_type(AddressSpace::Generic)
                .as_basic_type_enum()],
            true,
        );
        let printf_fn = self.module.add_function("printf", printf_ty, None);

        let digit_fmt = self.context.const_string(b"i32: %d\n", true);
        let digit_fmt_global = self.module.add_global(
            digit_fmt.get_type(),
            Some(AddressSpace::Global),
            "digit_fmt",
        );
        digit_fmt_global.set_initializer(&digit_fmt.as_basic_value_enum());

        let long_digit_fmt = self.context.const_string(b"i64: %lld\n", true);
        let long_digit_fmt_global = self.module.add_global(
            long_digit_fmt.get_type(),
            Some(AddressSpace::Global),
            "long_digit_fmt",
        );
        long_digit_fmt_global.set_initializer(&long_digit_fmt.as_basic_value_enum());

        let print_i32_signature = ast::FunctionSignature::new(
            "printI32".into(),
            vec![("value".into(), ast::Type::new("i32".into(), None))],
            ast::Type::new("unit".into(), None),
        );

        let print_i64_signature = ast::FunctionSignature::new(
            "printI64".into(),
            vec![("value".into(), ast::Type::new("i64".into(), None))],
            ast::Type::new("unit".into(), None),
        );

        let print_i32_fun = self.declare_function(print_i32_signature)?;
        let print_body = self.context.append_basic_block(print_i32_fun, "body");
        self.builder.position_at_end(print_body);
        self.builder.build_call(
            printf_fn,
            &[
                digit_fmt_global.as_basic_value_enum(),
                print_i32_fun.get_first_param().unwrap(),
            ],
            "call",
        );
        self.builder.build_return(None);

        let print_i64_fun = self.declare_function(print_i64_signature)?;
        let print_body = self.context.append_basic_block(print_i64_fun, "body");
        self.builder.position_at_end(print_body);
        self.builder.build_call(
            printf_fn,
            &[
                long_digit_fmt_global.as_basic_value_enum(),
                print_i64_fun.get_first_param().unwrap(),
            ],
            "call",
        );
        self.builder.build_return(None);

        let slice_type = ast::Type::new(
            "Slice".into(),
            Some(vec![ast::Type::new("u8".into(), None)]),
        );

        let len_signature = ast::FunctionSignature::new(
            "len".into(),
            vec![("slice".into(), slice_type.clone())],
            ast::Type::new("u64".into(), None),
        );

        let len_fun = self.declare_function(len_signature)?;
        let len_body = self.context.append_basic_block(len_fun, "body");
        let alloca = self.create_alloca(len_fun, "slice", &Type::Slice(box Type::UInt(8)))?;
        self.builder.position_at_end(len_body);
        self.builder
            .build_store(alloca, len_fun.get_first_param().unwrap());
        let len_field = unsafe { self.builder.build_struct_gep(alloca, 1, "len") };
        let len_value = self.builder.build_load(len_field, "len");
        self.builder.build_return(Some(&len_value));

        let data_signature = ast::FunctionSignature::new(
            "data".into(),
            vec![("slice".into(), slice_type.clone())],
            ast::Type::new(
                "Pointer".into(),
                Some(vec![ast::Type::new("u8".into(), None)]),
            ),
        );

        let data_fun = self.declare_function(data_signature)?;
        let data_body = self.context.append_basic_block(data_fun, "body");
        let alloca = self.create_alloca(data_fun, "slice", &Type::Slice(box Type::UInt(8)))?;
        self.builder.position_at_end(data_body);
        self.builder
            .build_store(alloca, data_fun.get_first_param().unwrap());
        let data_field = unsafe { self.builder.build_struct_gep(alloca, 0, "data") };
        let data_value = self.builder.build_load(data_field, "data");
        self.builder.build_return(Some(&data_value));

        let version_str = self.context.const_string(b"aoi v0.1", true);
        let version_str_global = self.module.add_global(
            version_str.get_type(),
            Some(AddressSpace::Global),
            "version_str",
        );
        version_str_global.set_initializer(&version_str.as_basic_value_enum());

        let version_signature = ast::FunctionSignature::new("version".into(), vec![], slice_type);

        let version_fun = self.declare_function(version_signature)?;
        let version_body = self.context.append_basic_block(version_fun, "name");
        self.builder.position_at_end(version_body);

        let version_slice = slice.const_named_struct(&[
            version_str_global.as_pointer_value().as_basic_value_enum(),
            self.context
                .i64_type()
                .const_int(9, false)
                .as_basic_value_enum(),
        ]);
        self.builder.build_return(Some(&version_slice));

        Ok(())
    }

    fn declare_function(&self, signature: ast::FunctionSignature) -> Result<FunctionValue> {
        let type_check = self.type_check.borrow();
        let return_ty = type_check.resolve(&signature.return_type).ok_or(anyhow!(
            "Error resolving function return type: {:?}",
            signature.return_type
        ))?;

        let mut argument_types = Vec::with_capacity(signature.arguments.len());
        let mut argument_names = Vec::with_capacity(signature.arguments.len());
        for (argument_name, argument_ty) in &signature.arguments {
            let argument_ty = type_check.resolve(&argument_ty).ok_or(anyhow!(
                "Error resolving function parameter type: {:?}",
                argument_ty
            ))?;
            argument_names.push(argument_name);
            argument_types.push(argument_ty);
        }

        let fun_ty = Type::function_type(&argument_types, &return_ty);
        let llvm_ty = fun_ty.map_to_llvm_function(self.context)?;

        let llvm_fun =
            self.module
                .add_function(&signature.identifier.name, llvm_ty, Some(Linkage::External));
        for (i, param) in llvm_fun.get_param_iter().enumerate() {
            match param {
                BasicValueEnum::IntValue(int) => int.set_name(&*argument_names[i].name),
                BasicValueEnum::FloatValue(float) => float.set_name(&*argument_names[i].name),
                BasicValueEnum::PointerValue(ptr) => ptr.set_name(&*argument_names[i].name),
                _ => {}
            }
        }

        let mut aoi = self.aoi.borrow_mut();
        aoi.add_signature(signature);

        Ok(llvm_fun)
    }
}

struct AoiContext<'a> {
    signatures: Vec<ast::FunctionSignature>,
    compiled: Vec<Option<FunctionValue<'a>>>,
}

impl<'a> AoiContext<'a> {
    fn new() -> Self {
        Self {
            signatures: Vec::new(),
            compiled: Vec::new(),
        }
    }

    fn add_signature(&mut self, signature: ast::FunctionSignature) {
        self.signatures.push(signature);
        self.compiled.push(None);
    }

    fn signature_of(&self, name: &str) -> Option<&ast::FunctionSignature> {
        for signature in self.signatures.iter() {
            if &*signature.identifier.name == name {
                return Some(signature);
            }
        }
        None
    }
}

#[derive(Clone, Debug)]
pub enum Type {
    Unit,
    Bool,
    F16,
    F32,
    F64,
    F128,
    Int(u32),
    UInt(u32),
    Pointer(Box<Type>),
    Slice(Box<Type>),
    Function(Vec<Type>, Box<Type>),
}

impl Type {
    fn value<'a>(self, llvm_value: LlvmValueWrapper<'a>) -> Value<'a> {
        Value::new(self, llvm_value)
    }

    fn is_same(&self, other: &Type) -> bool {
        use Type::*;
        match (self, other) {
            (Unit, Unit) => true,
            (Bool, Bool) => true,
            (F16, F16) => true,
            (F32, F32) => true,
            (F64, F64) => true,
            (F128, F128) => true,
            (Int(x), Int(y)) => x == y,
            (UInt(x), UInt(y)) => x == y,
            _ => false,
        }
    }

    fn function_type(arguments: &[Type], return_type: &Type) -> Type {
        Type::Function(arguments.to_vec(), box return_type.clone())
    }

    fn map_to_boolean<'a>(&self, context: &'a Context) -> Result<IntType<'a>> {
        match self {
            Type::Bool => Ok(context.bool_type()),
            _ => Err(anyhow!("Could not resolve type {:?} as boolean", self)),
        }
    }

    fn map_to_integer<'a>(&self, context: &'a Context) -> Result<IntType<'a>> {
        match self {
            Type::Int(size) | Type::UInt(size) => Ok(context.custom_width_int_type(*size)),
            _ => Err(anyhow!("Could not resolve type {:?} as integer", self)),
        }
    }

    fn map_to_float<'a>(&self, context: &'a Context) -> Result<FloatType<'a>> {
        match self {
            Type::F16 => Ok(context.f16_type()),
            Type::F32 => Ok(context.f32_type()),
            Type::F64 => Ok(context.f64_type()),
            Type::F128 => Ok(context.f128_type()),
            _ => Err(anyhow!("Could not resolve type {:?} as float", self)),
        }
    }

    fn map_to_llvm_basic<'a>(&self, context: &'a Context) -> Result<BasicTypeEnum<'a>> {
        match self {
            Type::Bool => Ok(context.bool_type().as_basic_type_enum()),
            Type::F16 => Ok(context.f16_type().as_basic_type_enum()),
            Type::F32 => Ok(context.f32_type().as_basic_type_enum()),
            Type::F64 => Ok(context.f64_type().as_basic_type_enum()),
            Type::F128 => Ok(context.f128_type().as_basic_type_enum()),
            Type::Int(size) | Type::UInt(size) => {
                Ok(context.custom_width_int_type(*size).as_basic_type_enum())
            }
            Type::Pointer(inner) => Ok(inner
                .map_to_llvm_basic(context)?
                .ptr_type(AddressSpace::Generic)
                .as_basic_type_enum()),
            Type::Slice(inner) => {
                let data = Type::Pointer((*inner).clone()).map_to_llvm_basic(context)?;
                let len = Type::UInt(64).map_to_llvm_basic(context)?;
                Ok(context
                    .struct_type(&[data, len], false)
                    .as_basic_type_enum())
            }
            Type::Function(..) => Ok(self
                .map_to_llvm_function(context)?
                .ptr_type(AddressSpace::Generic)
                .as_basic_type_enum()),
            _ => Err(anyhow!("Could not resolve basic type {:?}", self)),
        }
    }

    fn map_to_llvm_function<'a>(&self, context: &'a Context) -> Result<FunctionType<'a>> {
        match self {
            Type::Function(arguments, return_type) => {
                let mut argument_types = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    argument_types.push(argument.map_to_llvm_basic(context)?);
                }

                Ok(match &**return_type {
                    Type::Unit => context.void_type().fn_type(&argument_types, false),
                    ty => ty
                        .map_to_llvm_basic(context)?
                        .fn_type(&argument_types, false),
                })
            }
            _ => Err(anyhow!(
                "Tried to convert basic type {:?} to function",
                self
            )),
        }
    }
}

#[derive(Debug)]
pub struct Value<'a> {
    ty: Type,
    llvm_value: LlvmValueWrapper<'a>,
}

impl<'a> Value<'a> {
    fn new(ty: Type, llvm_value: LlvmValueWrapper<'a>) -> Self {
        Self { ty, llvm_value }
    }
}

#[derive(Debug)]
enum LlvmValueWrapper<'a> {
    Basic(BasicValueEnum<'a>),
    Any(AnyValueEnum<'a>),
}

impl<'a> LlvmValueWrapper<'a> {
    fn basic(self) -> Result<BasicValueEnum<'a>> {
        match self {
            LlvmValueWrapper::Basic(basic) => Ok(basic),
            _ => Err(anyhow!("Error getting basic llvm value"))?,
        }
    }

    fn any(self) -> Result<AnyValueEnum<'a>> {
        match self {
            LlvmValueWrapper::Any(any) => Ok(any),
            _ => Err(anyhow!("Error getting any llvm value"))?,
        }
    }
}

impl<'a> From<IntValue<'a>> for LlvmValueWrapper<'a> {
    fn from(int: IntValue<'a>) -> Self {
        Self::Basic(int.as_basic_value_enum())
    }
}

impl<'a> From<FloatValue<'a>> for LlvmValueWrapper<'a> {
    fn from(float: FloatValue<'a>) -> Self {
        Self::Basic(float.as_basic_value_enum())
    }
}

impl<'a> From<PointerValue<'a>> for LlvmValueWrapper<'a> {
    fn from(pointer: PointerValue<'a>) -> Self {
        Self::Basic(pointer.as_basic_value_enum())
    }
}

impl<'a> From<BasicValueEnum<'a>> for LlvmValueWrapper<'a> {
    fn from(basic: BasicValueEnum<'a>) -> Self {
        Self::Basic(basic)
    }
}

impl<'a> From<FunctionValue<'a>> for LlvmValueWrapper<'a> {
    fn from(function: FunctionValue<'a>) -> Self {
        Self::Any(function.as_any_value_enum())
    }
}

pub struct TypeCheck {
    known: Vec<Type>,
}

impl TypeCheck {
    pub fn new() -> Self {
        Self { known: Vec::new() }
    }

    pub fn resolve(&self, from: &ast::Type) -> Option<Type> {
        let ast::Type {
            identifier: ast::Identifier { name },
            generics,
        } = from;
        match &**name {
            "unit" => Some(Type::Unit),
            "bool" => Some(Type::Bool),
            "f16" => Some(Type::F16),
            "f32" => Some(Type::F32),
            "f64" => Some(Type::F64),
            "f128" => Some(Type::F128),
            "Pointer" => {
                let inner = generics.as_ref()?;
                if inner.len() != 1 {
                    None
                } else {
                    Some(Type::Pointer(box (self.resolve(&inner[0])?)))
                }
            }
            "Slice" => {
                let inner = generics.as_ref()?;
                if inner.len() != 1 {
                    None
                } else {
                    Some(Type::Slice(box (self.resolve(&inner[0])?)))
                }
            }
            _ => self.integer(&*name),
        }
    }

    fn integer(&self, name: &str) -> Option<Type> {
        if name.starts_with('i') {
            let size = name[1..].parse::<u32>().ok()?;
            Some(Type::Int(size))
        } else if name.starts_with('u') {
            let size = name[1..].parse::<u32>().ok()?;
            Some(Type::UInt(size))
        } else {
            None
        }
    }
}
