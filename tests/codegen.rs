use aoi::{codegen::Codegen, parser::Parser};
use inkwell::context::Context;

#[test]
fn return_i32() {
    simple_test("fun main() i32 -> 1", 1);
    simple_test("fun main() i32 -> 2", 2);
    simple_test("fun main() i32 -> 4", 4);
}

#[test]
fn call_func() {
    simple_test(
        "fun x(a i16, b i32, c i64) i32 -> b
        fun main() i32 -> x(1, 2, 3)",
        2,
    );
    simple_test(
        "fun x(a i16, b i32, c i64) i32 -> b
        fun main() i32 -> {
            let a = 1
            a.x(2, 3)
        }",
        2,
    );
}

#[test]
fn call_extern() {
    simple_test(
        "fun putchar(char i32) i32 extern
        fun main() i32 -> putchar(65)",
        65,
    );
}

#[test]
fn variables() {
    simple_test(
        "fun a(x i32) i32 -> let y = x
        fun main() i32 -> {
            let z = a(100)
            z.a()
        }",
        100,
    );
}

#[test]
fn if_expr() {
    simple_test("fun main() i32 -> if true 4 else 8", 4);
    simple_test("fun main() i32 -> if false 4 else 8", 8);
}

#[test]
fn everything() {
    simple_test(
        "fun puts(str *u8) i32 extern
        fun precedence(x i32, y i32, z i32) i32 -> x + y * z
        fun not(value bool) bool -> if value false else true
        fun main() i32 -> {
            puts(\"everything works!\")
            let val = if false.not() precedence(1, 2, 4) else { 0 } // 1 + (2 * 4)
            val = val + val // 9 + 9
        }",
        18,
    );
}

fn simple_test(code: &str, expect: i32) {
    let mut code = code.to_string();
    code.push(' ');

    let mut parser = Parser::new(&code);
    let program = parser.parse_program().expect("Error parsing program");
    let context = Context::create();
    let codegen = Codegen::new(&context, false, false);
    let result = codegen.compile(program).expect("Error compiling program");
    assert_eq!(result, expect)
}
