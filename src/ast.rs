macro_rules! enum_structs {
    (#[$attr:meta] $visiblity:vis enum $name:ident { $($field:ident( $($v:vis $f:ident : $t:ty),* )),* $(,)? }) => {
        #[$attr]
        $visiblity enum $name {
            $($field($field),)*
        }
        $(
            #[$attr]
            $visiblity struct $field {
                $($v $f: $t,)*
            }

            impl From<$field> for $name {
                #[inline]
                fn from(value: $field) -> Self {
                    Self::$field(value)
                }
            }
        )*
    };
}

enum_structs! {
    #[derive(Clone, Debug, PartialEq)]
    pub enum Expression {
        Program(pub expressions: Vec<Expression>),
        Function(pub signature: FunctionSignature, pub body: FunctionBody),
        Block(pub expressions: Vec<Expression>),
        Integer(pub value: u64),
        Float(pub value: f64),
        Bool(pub value: bool),
        String(pub value: Box<str>),
        Type(pub identifier: Identifier, pub generics: Option<Vec<Type>>),
        Identifier(pub name: Box<str>),
        Assign(pub identifier: Identifier, pub expression: Box<Expression>),
        UnaryOp(pub op: Box<str>, pub expression: Box<Expression>),
        BinaryOp(pub lhs: Box<Expression>, pub op: Box<str>, pub rhs: Box<Expression>),
        Call(pub identifier: Identifier, pub arguments: Vec<Expression>),
        If(pub condition: Box<Expression>, pub then: Box<Expression>, pub other: Option<Box<Expression>>),
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct FunctionSignature {
    pub identifier: Identifier,
    pub arguments: Vec<(Identifier, Type)>,
    pub return_type: Type,
}

#[derive(Clone, Debug, PartialEq)]
pub enum FunctionBody {
    Extern,
    Body(Box<Expression>),
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

impl Float {
    pub fn new(value: f64) -> Self {
        Self { value }
    }
}

impl From<f64> for Float {
    fn from(value: f64) -> Self {
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
