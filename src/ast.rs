#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expression {
    Program(Program),
    Function(Function),
    Block(Block),
    Integer(Integer),
    Bool(Bool),
    String(String),
    Type(Type),
    Identifier(Identifier),
    Assign(Assign),
    Return(Return),
    UnaryOp(UnaryOp),
    BinaryOp(BinaryOp),
    Call(Call),
    If(If),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program {
    pub expressions: Vec<Expression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function {
    pub signature: FunctionSignature,
    pub body: FunctionBody,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionSignature {
    pub identifier: Identifier,
    pub arguments: Vec<(Identifier, Type)>,
    pub return_type: Type,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FunctionBody {
    Extern,
    Body(Box<Expression>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block {
    pub expressions: Vec<Expression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Integer {
    pub value: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Bool {
    pub value: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct String {
    pub value: Box<str>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Identifier {
    pub name: Box<str>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Type {
    pub identifier: Identifier,
    pub generics: Option<Vec<Type>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct If {
    pub condition: Box<Expression>,
    pub then: Box<Expression>,
    pub other: Option<Box<Expression>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Assign {
    pub identifier: Identifier,
    pub expression: Box<Expression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Return {
    pub expression: Box<Expression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnaryOp {
    pub op: Box<str>,
    pub expression: Box<Expression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinaryOp {
    pub lhs: Box<Expression>,
    pub op: Box<str>,
    pub rhs: Box<Expression>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Call {
    pub identifier: Identifier,
    pub arguments: Vec<Expression>,
}

impl Identifier {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string().into_boxed_str(),
        }
    }
}

impl From<&str> for Identifier {
    fn from(name: &str) -> Self {
        Self::new(name)
    }
}

impl Integer {
    pub fn new(value: u64) -> Self {
        Self { value }
    }
}

impl From<u64> for Integer {
    fn from(value: u64) -> Self {
        Self::new(value)
    }
}

impl Bool {
    pub fn new(value: bool) -> Self {
        Self { value }
    }
}

impl String {
    pub fn new(value: &str) -> Self {
        Self {
            value: value.to_string().into_boxed_str(),
        }
    }
}

impl UnaryOp {
    pub fn new(op: &str, expression: Expression) -> Self {
        Self {
            op: op.into(),
            expression: box expression,
        }
    }
}

impl BinaryOp {
    pub fn new(lhs: Expression, op: &str, rhs: Expression) -> Self {
        Self {
            lhs: box lhs,
            op: op.into(),
            rhs: box rhs,
        }
    }
}

impl Type {
    pub fn new(identifier: Identifier, generics: Option<Vec<Type>>) -> Self {
        Self {
            identifier,
            generics,
        }
    }
}

impl Function {
    pub fn new(signature: FunctionSignature, body: Expression) -> Self {
        Self {
            signature,
            body: FunctionBody::Body(box body),
        }
    }

    pub fn new_extern(signature: FunctionSignature) -> Self {
        Self {
            signature,
            body: FunctionBody::Extern,
        }
    }
}

impl FunctionSignature {
    pub fn new(
        identifier: Identifier,
        arguments: Vec<(Identifier, Type)>,
        return_type: Type,
    ) -> Self {
        Self {
            identifier,
            arguments,
            return_type,
        }
    }
}

impl Block {
    pub fn new(expressions: Vec<Expression>) -> Self {
        Self { expressions }
    }
}

impl Assign {
    pub fn new(identifier: Identifier, expression: Expression) -> Self {
        Self {
            identifier,
            expression: box expression,
        }
    }
}

impl Call {
    pub fn new(identifier: Identifier, arguments: Vec<Expression>) -> Self {
        Self {
            identifier,
            arguments,
        }
    }
}

impl If {
    pub fn new(condition: Expression, then: Expression, other: Option<Expression>) -> Self {
        Self {
            condition: box condition,
            then: box then,
            other: other.map(Box::new),
        }
    }
}

macro_rules! impl_trivial_from {
    (for $t:ty { $($param:ident : $variant:ident),* $(,)? }) => {
        $(
            impl From<$variant> for $t {
                #[inline]
                fn from($param: $variant) -> Self {
                    Self::$variant($param)
                }
            }
        )*
    };
}

impl_trivial_from!(for Expression {
    program: Program,
    function: Function,
    block: Block,
    integer: Integer,
    r#bool: Bool,
    string: String,
    r#type: Type,
    identifier: Identifier,
    assign: Assign,
    r#return: Return,
    binary_op: BinaryOp,
    unary_op: UnaryOp,
    call: Call,
    r#if: If,
});
