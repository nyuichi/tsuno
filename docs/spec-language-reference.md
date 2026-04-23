# Spec Language Reference

This document describes the spec language that is implemented today. It covers only the language itself: where spec code may appear, which expressions are accepted, how binders work, and which forms are currently rejected.

The language appears in two places:

- line directives such as `//@ req`, `//@ ens`, `//@ assert`, `//@ assume`, `//@ inv`, and `//@ lemma_name(...)`
- ghost blocks written as `/*@ ... */`

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

Rules:

- a function may omit the contract entirely
- if a contract is present, it must contain exactly one `//@ req` and exactly one `//@ ens`
- both lines must appear immediately before the body
- `result` is only available bare in `//@ ens`

Assertions, assumptions, and lemma calls appear inside executable Rust code.

```rust
//@ assert {x} == 0;
//@ assume {x} == 0;
//@ helper_lemma({x});
```

Rules:

- these forms require a trailing `;`
- the expression is written directly; it is not wrapped in a string literal

Loop invariants appear immediately before the loop body.

```rust
while x < n
  //@ inv 0 <= {x} && {x} <= {n}
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
?x
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

This matters for binders as well. For example:

```text
!P(?x) == !(P(?x))
```

## 3. Spec Binders

The form `?x` introduces a spec binder. A binder is not a general existential form. It is a witness-style binding syntax with a restricted shape.

```rust
//@ assert ?V == *{r};
//@ assert V == *{r};
```

```rust
fn read_ref(x: &i32) -> i32
//@ req ?V == *{x}
//@ ens V == result
{
    *x
}
```

In runtime specs, an unprefixed name such as `V` refers to a spec binder that has already been introduced and is visible at that point.

In ghost blocks, an unprefixed name may also refer to an ordinary ghost parameter or local binding.

If no visible binding exists, the expression is rejected.

### 3.1 Binder-Introducing Forms

New binders may be introduced only in:

- `req`
- `//@ assert`
- ghost `assert`

In those positions, binder introduction is allowed only through top-level conjunctions whose conjunct has the form:

```text
?x == expr
```

Examples:

```text
assert ?x == 42 && Q(x);   // ok
assert ?x == 42 && ?y == x && R(x, y);   // ok
assert Q(x) && ?x == 42;   // rejected
assert !P(?x);             // rejected
assert 42 == ?x;           // rejected
```

The accepted form is processed left to right. Conceptually:

```text
assert ?x == 42 && ?y == x && R(x, y);

== let x = 42;
   let y = x;
   assert R(x, y);
```

The surface language does not have `let`. This desugaring describes the implemented behavior.

### 3.2 Scope Across `req`, Body Directives, and `ens`

Function-level binder visibility is staged in source order:

1. `req`
2. body directives such as `assert`, `assume`, `inv`, and lemma calls
3. `ens`

As a result, binders introduced in `req` are available both in later body directives and in the matching `ens`.

```rust
fn f(x: &i32) -> i32
//@ req ?V == *{x}
//@ ens true
{
    //@ assert V == *{x};
    *x
}
```

```rust
fn read_ref(x: &i32) -> i32
//@ req ?V == *{x}
//@ ens V == result
{
    *x
}
```

Binders introduced in a function body are available later in that body.

```rust
fn main() {
    let x = 1;
    let r = &x;
    //@ assert ?V == *{r};
    //@ assert V == *{r};
}
```

Binders introduced only in one directive are visible to later directives, not earlier ones.

New binders are rejected in:

- `ens`
- `//@ assume`
- `//@ inv`
- ghost `assume`

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
//@ req ?Old == *{xs}
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
- pure functions: `fn name(args...) -> Ty { expr }`
- lemmas: `fn name<T>(args...) req <expr> ens <expr> { stmts }`

Pure function bodies are expression bodies. Lemma bodies are statement bodies.

Supported lemma statements:

- `assert expr;`
- `assume expr;`
- `lemma_name(args...);`
- `match scrutinee { ... }`

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

- generic pure function definitions are rejected
- generic lemmas are accepted
- explicit type arguments are supported for enum constructors and lemma calls, but not for pure function calls
- statement-level `match` default arms must come last
- expression-level `match` may contain at most one `_` arm
