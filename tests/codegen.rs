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
        fun cast(a i16) i16 -> a
        fun main() i32 -> {
            let a = cast(1)
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
fn call_overloads() {
    simple_test(
        "fun puts(str *u8) i32 extern
        fun overload(str *u8) *u8 -> str
        fun overload(x i32) i32 -> x
        fun overload(x f64) f64 -> x

        fun main() -> {
            puts(overload(\"str\"))
            let a = overload(2.3)
            let b = overload(100)
            b
        }
        ",
        100,
    );
    simple_test(
        "fun puts(str *u8) i32 extern
        fun complex(a bool, x f64, z *u8) -> if a x.print() else puts(z)
        fun complex(a bool, x i32, z *u8) i32 -> if a { x.print() x + 1 } else { puts(z) 0 }

        fun main() i32 -> {
            let str = \"shouldn't be printed\"
            complex(true, 13.0, str)
            complex(true, 4, str) // if true 4 + 1
        }
        ",
        5,
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
    simple_test(
        "fun unit(x i32, y f64) -> if false x.print() else print(y) 
        fun main() i32 -> {
            unit(1, 1)
            2
        }",
        2,
    );
}

#[test]
fn floats() {
    simple_test(
        "fun floats(x f64) f64 -> {
            let y = x + 1.0
            y
        }
        fun main() i32 -> {
            let a = floats(4.0)
            0
        }",
        0,
    );
}

#[test]
fn everything() {
    simple_test(
        "fun puts(str *u8) i32 extern
        fun precedence(x i32, y i32, z i64) i32 -> 0
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
    let codegen = Codegen::new(&context, true, false, true);
    let result = codegen.compile(program).expect("Error compiling program");
    assert_eq!(result, expect)
}
