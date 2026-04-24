# Spec Language Reference

This document describes the spec language that is implemented today. It covers only the language itself: where spec code may appear, which expressions are accepted, how binders work, and which forms are currently rejected.

The language appears in two places:

- directives written in spec comments, such as `//@ let`, `//@ req`, `//@ ens`, `//@ assert`, `//@ assume`, `//@ inv`, and `//@ lemma_name(...)`
- ghost item blocks written as `/*@ ... */` whose contents begin with `fn` or `enum`

## 1. Where Spec Code Appears

Function contracts are written immediately before the function body.

```rust
fn add1(x: i32) -> i32
//@ req {x} >= 0
//@ ens result == {x} + 1
{
    x + 1
}
```

The line form `//@` and the block form `/*@ ... */` are treated like one stream of doc comments. Consecutive comments are joined before parsing, so a predicate may be split across both forms.

```rust
fn add1(x: i32) -> i32
//@ req {x} >= 0 &&
/*@    {x} <= 2147483647 */
//@ ens result == {x} + 1
{
    x + 1
}
```

Multiple contract directives may also appear in one spec comment.

```rust
fn id(x: i32) -> i32
//@ req true ens result == {x}
{
    x
}
```

Rules:

- a function may omit the contract entirely
- if a contract is present, it must contain exactly one `//@ req` and exactly one `//@ ens`
- both lines must appear immediately before the body
- `result` is only available bare in `//@ ens`

Let bindings, assertions, assumptions, and lemma calls appear inside executable Rust code.

```rust
//@ let old = {x};
//@ assert {x} == 0;
//@ assume {x} == 0;
//@ helper_lemma({x});
```

Block comments may be used for statement directives as well.

```rust
/*@ assert {x} == {x} &&
    true; */
```

Rules:

- `//@ let name = expr;`, `//@ assert`, `//@ assume`, and lemma calls require a trailing `;`
- the expression is written directly; it is not wrapped in a string literal

Loop invariants appear immediately before the loop body.

```rust
while x < n
  //@ inv 0 <= {x} && {x} <= {n}
{
    x = x + 1;
}
```

The block form is equivalent here too.

```rust
while x < n
  /*@ inv 0 <= {x} && {x} <= {n} */
{
    x = x + 1;
}
```

Rules:

- each supported loop must have exactly one `//@ inv`
- the invariant must be attached to the loop header, not placed later inside the body

## 2. Writing Expressions

Spec expressions are written directly. In runtime specs (`req`, `ens`, `assert`, `assume`, `inv`, and runtime lemma calls), a bare identifier refers only to a visible spec binder. The only built-in bare name is `result` in `ens`. A Rust binding must be written as `{name}`.

```rust
//@ assert {x} == 1i32;
//@ assert *{r} == 1i32;
//@ assert {pair}.left == 1i32;
//@ assert {pair}.0 == 1i32;
```

Inside ghost blocks, ordinary ghost parameters and local names are written bare.

```rust
/*@
fn add1(x: i32) -> i32 {
    x + 1i32
}
*/
```

Ghost item blocks can also be written with line comments, or by mixing line and block comments.

```rust
//@ fn trivial(n: Nat)
//@   req true
//@   ens true
//@ {}

/*@ fn also_trivial(n: Nat) */
//@   req true
/*@   ens true */
//@ {}
```

Interpolation composes with the surrounding spec syntax. The content of `{...}` is a single Rust binding name, not a general Rust expression.

```text
{x}
*{r}
{pair}.0
```

String-literal wrappers are not part of the language.

```rust
//@ assert "{x} == 1i32";
```

The form above is rejected.

### 2.1 Expression Forms

The parser accepts the following expression forms.

```text
true
false
0
1i32
42usize
result
x
{x}
f(x, y)
Enum::Ctor(x, y)
Enum::<T>::Ctor(x)
(expr)
[a, b, c]
xs[i]
expr.field
expr.0
*expr
-expr
!expr
lhs + rhs
lhs - rhs
lhs * rhs
lhs ++ rhs
lhs == rhs
lhs != rhs
lhs < rhs
lhs <= rhs
lhs > rhs
lhs >= rhs
lhs && rhs
lhs || rhs
```

### 2.2 Precedence and Associativity

The operator precedence, from tightest to loosest, is:

```text
1. postfix        .field   .0   [i]
2. unary          !   -   *
3. multiplicative *
4. additive       +   -
5. sequence concat ++
6. comparison     <   <=   >   >=
7. equality       ==   !=
8. conjunction    &&
9. disjunction    ||
```

Binary operators are left-associative within each precedence level.

```text
a - b - c      == (a - b) - c
a ++ b ++ c    == (a ++ b) ++ c
a && b && c    == (a && b) && c
```

## 3. Spec Binders

The directive `//@ let name = expr;` introduces a spec binder. The right-hand side is a spec expression evaluated at that program point.

```rust
//@ let V = *{r};
//@ assert V == *{r};
```

```rust
fn read_ref(x: &i32) -> i32
//@ let V = *{x};
//@ req true
//@ ens V == result
{
    *x
}
```

In runtime specs, an unprefixed name such as `V` refers to a spec binder that has already been introduced and is visible at that point.

In ghost blocks, an unprefixed name may also refer to an ordinary ghost parameter or local binding.

If no visible binding exists, the expression is rejected.

### 3.1 Binder-Introducing Forms

New binders may be introduced with `//@ let` before a function contract's `//@ req`, or inside executable Rust code.

```rust
fn f(x: usize)
//@ let y = {x};
//@ let z = y;
//@ req z == {x}
//@ ens result == z
{
    z
}
```

```rust
fn g(x: i32) {
    //@ let y = {x};
    //@ assert y == {x};
}
```

The old `?x` binder syntax is not part of the language.

```rust
//@ assert ?x == 42usize;
```

The form above is rejected.

### 3.2 Scope Across `req`, Body Directives, and `ens`

Spec binders follow the corresponding Rust source scope.

Function-level `//@ let` directives before `//@ req` are visible in the function's `req`, body directives, and `ens`.

```rust
fn read_ref(x: &i32) -> i32
//@ let V = *{x};
//@ req true
//@ ens result == V
{
    *x
}
```

Body `//@ let` directives are available to later directives in the same Rust scope. A binder introduced in an inner block is not visible after that block.

```rust
fn main() {
    let x = 1;
    let r = &x;
    {
        //@ let V = *{r};
        //@ assert V == *{r};
    }
    //@ assert {x} == {x};
}
```

Binders are visible only after their `//@ let` directive; forward references are rejected.

## 4. Types and Values

The surface type syntax accepts:

```text
bool
i8   i16   i32   i64   isize
u8   u16   u32   u64   usize
Seq<T>
Name
Name<T1, T2, ...>
T
```

Examples:

```rust
enum List<T> {
    Nil,
    Cons(T, List<T>),
}

fn len(xs: List<i32>) -> i32 { ... }
```

Integer literals may be unsuffixed or use one of the integer suffixes above.

```text
0
1i32
42usize
18446744073709551615u64
```

Equality and inequality require matching spec types. Equality on `Ref<T>` and `Mut<T>` is currently rejected.

## 5. References, Fields, Tuples, and Sequences

Shared references can be dereferenced with `*`.

```rust
//@ assert *{x} == {y};
```

Mutable references expose both the current value through `*` and the final value through `.fin`.

```rust
//@ let Old = *{xs};
//@ req true
//@ ens {xs}.fin == Old ++ [x]
```

Named field access works on structs.

```rust
//@ assert {pair}.left == 0i32;
```

Numeric projection works on tuples.

```rust
//@ assert {pair}.0 == 0i32;
```

Sequence literals, concatenation, and indexing are part of the language.

```rust
//@ assert [1i32, 2i32] ++ [3i32] == [1i32, 2i32, 3i32];
//@ assert ([1i32, 2i32])[Nat::Zero] == 1i32;
```

## 6. Ghost Blocks

Ghost blocks define additional spec-side items.

```rust
/*@
enum List<T> {
    Nil,
    Cons(T, List<T>),
}

fn len(xs: List<i32>) -> i32 {
    match xs {
        List::Nil => 0i32,
        List::Cons(_, xs0) => 1i32 + len(xs0),
    }
}

fn append_len(xs: List<i32>, ys: List<i32>)
  req true
  ens len(append(xs, ys)) == len(xs) + len(ys)
{
    match xs {
        List::Nil => {
            assert len(append(xs, ys)) == len(xs) + len(ys);
        }
        List::Cons(_, xs0) => {
            append_len(xs0, ys);
            assert len(append(xs, ys)) == len(xs) + len(ys);
        }
    }
}
*/
```

Supported items:

- `enum`
- pure functions: `fn name<T>(args...) -> Ty { expr }`
- lemmas: `fn name<T>(args...) req <expr> ens <expr> { stmts }`

Pure function bodies are expression bodies. Lemma bodies are statement bodies.

Supported lemma statements:

- `assert expr;`
- `assume expr;`
- `lemma_name(args...);`
- `match scrutinee { ... }`

Explicit type arguments use Rust-style `::<...>` syntax.

```rust
List::Cons::<i32>(0i32, List::Nil::<i32>)
seq_rev::<i32>(xs)
append_len::<i32>(xs, ys);
```

### 6.1 Match

`match` expressions are supported in pure function bodies.

```rust
fn len(xs: List<i32>) -> i32 {
    match xs {
        List::Nil => 0i32,
        List::Cons(_, xs0) => 1i32 + len(xs0),
    }
}
```

Lemma bodies support statement-level `match`.

```rust
match xs {
    List::Nil => {
        assert true;
    }
    List::Cons(_, xs0) => {
        append_len(xs0, ys);
    }
}
```

Patterns have the form:

```text
Enum::Ctor
Enum::Ctor(x, y)
Enum::Ctor(_, xs0)
_
```

Rules:

- builtin pure functions do not accept explicit type arguments
- statement-level `match` default arms must come last
- expression-level `match` may contain at most one `_` arm
