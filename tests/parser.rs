use aoi::{ast::*, parser::Parser};
use std::vec as ast;

#[test]
fn binary() {
    test(
        "1 + 64.0",
        ast![BinaryOp::new(Integer::new(1).into(), "+", Float::new(64.0).into()).into()],
    );

    test(
        "2 + 128 * 256",
        ast![BinaryOp::new(
            Integer::new(2).into(),
            "+",
            BinaryOp::new(Integer::new(128).into(), "*", Integer::new(256).into()).into()
        )
        .into()],
    );
}

#[test]
fn unary() {
    test(
        "!true + -0",
        ast![BinaryOp::new(
            UnaryOp::new("!", Bool::new(true).into()).into(),
            "+",
            UnaryOp::new("-", Integer::new(0).into()).into(),
        )
        .into()],
    );
}

#[test]
fn grouping() {
    test(
        "((2 + 128) * 256)",
        ast![BinaryOp::new(
            BinaryOp::new(Integer::new(2).into(), "+", Integer::new(128).into()).into(),
            "*",
            Integer::new(256).into(),
        )
        .into()],
    );
}

#[test]
fn function() {
    test(
        "fun putchar(char i32) i32 extern",
        ast![Function::new_extern(FunctionSignature::new(
            "putchar".into(),
            vec![("char".into(), Type::new("i32".into(), None))],
            Type::new("i32".into(), None)
        ))
        .into()],
    );
    test(
        "fun putchar(char i32) i32 -> char",
        ast![Function::new(
            FunctionSignature::new(
                "putchar".into(),
                vec![("char".into(), Type::new("i32".into(), None))],
                Type::new("i32".into(), None)
            ),
            Identifier::new("char").into()
        )
        .into()],
    );
}

#[test]
fn assign() {
    test(
        "let hello = \"world\"",
        ast![Assign::new("hello".into(), String::new("world").into()).into()],
    );

    test(
        "let sum = let a = -10",
        ast![Assign::new(
            "sum".into(),
            Assign::new(
                "a".into(),
                UnaryOp::new("-", Integer::new(10).into()).into()
            )
            .into()
        )
        .into()],
    );
}

#[test]
fn block() {
    test(
        "{ 1 + 2 3.0 }",
        ast![Block::new(vec![
            BinaryOp::new(Integer::new(1).into(), "+", Integer::new(2).into()).into(),
            Float::new(3.0).into()
        ])
        .into()],
    );
}

#[test]
fn program() {
    let pointer_u8 = Type::new("Pointer".into(), Some(vec![Type::new("u8".into(), None)]));
    test(
        "fun puts(str *u8) i32 extern
        fun get(cond bool) *u8 -> \"str\"
        fun main() i32 -> {
            let str = get()
            puts(str)
            0
        }
        ",
        ast![
            Function::new_extern(FunctionSignature::new(
                "puts".into(),
                vec![("str".into(), pointer_u8.clone())],
                Type::new("i32".into(), None)
            ))
            .into(),
            Function::new(
                FunctionSignature::new(
                    "get".into(),
                    vec![("cond".into(), Type::new("bool".into(), None))],
                    pointer_u8
                ),
                String::new("str").into()
            )
            .into(),
            Function::new(
                FunctionSignature::new("main".into(), vec![], Type::new("i32".into(), None)),
                Block::new(vec![
                    Assign::new("str".into(), Call::new("get".into(), vec![]).into()).into(),
                    Call::new("puts".into(), vec![Identifier::new("str").into()]).into(),
                    Integer::new(0).into()
                ])
                .into()
            )
            .into()
        ],
    );
}

fn test(code: &str, expect: impl AsRef<[Expression]>) {
    let mut parser = Parser::new(code);
    let program = parser.parse_program().expect("Error parsing program");
    let expect = expect.as_ref();
    assert_eq!(program.expressions.len(), expect.len());
    for (expr, expect) in program.expressions.iter().zip(expect.iter()) {
        assert_eq!(*expr, *expect)
    }
}
