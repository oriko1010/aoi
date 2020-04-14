### Data types

Aoi has several built-in data types

Identifier | Type
--- | ---
unit | zero-sized type
bool | boolean
i{1..} | arbitrary size signed integer
u{1..} | arbitrary size unsigned integer
f16 | 16-bit floating point
f32 | 32-bit floating point
f64 | 64-bit floating point
f128 | 128-bit floating point
*T | pointer to T
[]T | slice of T with a u64 length

### Variables

A variable can be assigned with a `let` keyword, an identifier, a `=` token and an expression. A `let` expression returns the newly assigned value. The variable type is inferred from the expression.
```
fun add(x u64, y u64) u64 -> {
    let sum = x + y
    sum
}

// Assigns to variable div and immediately returns the assigned value
fun immediate(x f64) f64 -> let div = x / 1
```

### Functions

A `function signature` starts with a `fun` keyword, has a name, an argument list, and an optional return type. If no return type is specifier, `unit` is implied.  
After the signature can come either a `function literal` or an `extern` keyword. A `function literal` starts with a `->` token and any expression after. The expression will be target typed to the function's return type.  

```
fun putchar(char i32) i32 extern
fun printNewline() -> putchar(10)

fun print(char i32) -> {
    putchar(10)
    printNewline()
}
```

### Function calls

A function is called by it's identifier being followed with a `(`, a list of expressions separated by a `,` and a `)`. Special cased is an expression being followed by a `.` and then the function identifier, which desugars the expression as the first argument.

```
fun add(a i32, b i32) i32 -> a + b

fun main() i32 -> {
    let x = 4.add(5)  // Parsed as add(4, 5)
    let x = add(x, 6) // Works too
}
```

Functions may be overloaded by their argument types.

```
fun add(a i32, b i32) i32 -> a + b
fun add(a f64, b f64) f64 -> a + b

fun main() i32 -> {
    let x = add(3, 3) // i32(6)
    let y = add(4.5, 4.5) // f64(9.0)
    x
}
```

### Literals

A `bool literal` expression is either `true` or `false`. Always evaluates to `bool` type.

```
let t = true  // bool(true)
let f = false // bool(false)
```

An `integer literal` expression is any whole number. The literal expression is target typed and defaults to `i32` if no target type exists.

```
fun long(x i64) i64 -> x
let l = long(8) // i64(8)
let i = 8       // i32(8)
```


A `float literal` expression is a number with a decimal point `.`, followed by a fractional part. Neither part can be omitted, i.e. `1.` or `.1` do not work. The literal expression is target typed and defaults to `f64` if no target type exists.

```
fun float(x f32) f32 -> x
let f = float(16.0) // f32(16.0)
let d = 16.0        // f64(16.0)
```

A `string literal` expression is any text surrounded by `"` quotes. The type of the expression is `*u8`. Currently null-terminated.

```
fun puts(str *u8) i32 extern

fun main() -> {
    let str = "Hello, world!"
    puts(str)
}
```

### If expressions

An `if` expression starts with an `if` keyword, a condition expression, a then expression and an optional `else` keyword followed by an else expression.  
The condition expression has to be a `bool` type (note: despite being the same in LLVM, `bool` and `{i,u}1` are not compatible).  
The then and else expressions have to be of the same type. The expression evaluates to the successful branch.

```
fun short(cond bool) i128 -> if cond 2 else 4 + 8

fun explicit(cond bool) i128 -> {
    if cond { 2 } else { 4 + 8 }
}
```

### Block expressions

A block expression starts with a `{` and contains a list of expressions ending with `}`. The expression evaluates to the last value in the list. Any variables are scoped within the block and cannot be accessed outside of it.
```
fun block(x f64, y f64) f64 -> { // this is a block too
    let value = {
        let a = x + y
        let b = x * y
        b - a
    }
    value
}
```
