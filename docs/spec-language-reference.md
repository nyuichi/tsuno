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
//@ ens {result} == {x} + 1
{
    x + 1
}
```

Rules:

- a function may omit the contract entirely
- if a contract is present, it must contain exactly one `//@ req` and exactly one `//@ ens`
- both lines must appear immediately before the body
- `result` is only available in `//@ ens`

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

Spec expressions are written directly. In-scope names may be used directly, and `{...}` may be used to splice a Rust expression into spec syntax.

```rust
//@ assert x == 1i32;
//@ assert {x} == 1i32;
//@ assert *{r} == 1i32;
//@ assert {pair}.left == 1i32;
//@ assert {pair}.0 == 1i32;
```

Interpolation is syntactic. The inserted Rust expression is parenthesized before parsing as spec syntax.

```text
{x}      => (x)
*{r}     => *(r)
{pair}.0 => (pair).0
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
x
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

## 3. Existential Binders

The form `?x` introduces a spec binder. A binder can be introduced in a contract, assertion, assumption, or invariant, and then referred to later by its bare name.

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

An unprefixed name such as `V` refers to:

- a spec binder that has already been introduced and is visible at that point
- otherwise a visible Rust binding

If no visible binding exists, the expression is rejected.

### 3.1 Introduction Order and Existential Checking

A binder is introduced by writing `?x`. Introduction is source-ordered: a later bare use may refer to that binder, but an earlier bare use may not.

```text
assert ?x == 42 && Q(x);   // ok
assert Q(x) && ?x == 42;   // rejected: `x` is still unresolved at the left-hand use
```

After parsing and name resolution, any assertion-like directive that contains at least one binder is checked existentially.

```text
assert ?x == 42;
== exists x. x == 42
```

```text
assert ?x == 42 && Q(x);
== exists x. x == 42 && Q(x)
```

```text
assert !P(?x);
== exists x. !P(x)
```

So `assert !P(?x);` does not mean `!exists x. P(x)` and does not mean `forall x. !P(x)`. The `!` still applies only to `P(?x)`, and the enclosing assertion is then checked existentially.

### 3.2 Witness Equalities

The verifier also has an implementation-specific proof shortcut for top-level conjunctions. Inside a `&&` chain, equalities of the following forms are extracted eagerly as witnesses:

```text
?x == e
e == ?x
```

Example:

```text
?x == e && ?y == f(x) && R(x, y)
```

The extracted witnesses are `x = e` and `y = f(x)`, then `R(x, y)` is checked.

Other shapes are still existential, but they are not extracted as direct witnesses.

```text
!P(?x)
P(?x) || Q
?x == f(?x)
```

This shortcut does not define binder scope. It only changes how certain conjunctions are discharged.

### 3.3 Scope Across `req`, Body Directives, and `ens`

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

Binders introduced only in `ens` are not visible in the function body, and a binder introduced later in a directive does not retroactively bind an earlier bare use.

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

## 7. Current Restrictions

The following forms are rejected by the current implementation:

- string-literal-wrapped spec expressions such as `//@ assert "{x} == 1";`
- `match` expressions in `req`, `ens`, `assert`, `assume`, or `inv`
- use of `result` outside `ens`
- equality or inequality on `Ref<T>` or `Mut<T>`
- tuple projection on non-tuples
- tuple projection on structs
- named field access on non-structs, except `.fin` on `Mut<T>`
- loops without exactly one attached `//@ inv`
- function contracts that are not placed immediately before the body

Examples of rejected forms:

```rust
//@ req {result} == 1
//@ assert {r} == {r}
//@ assert match xs { ... }
//@ assert "{x} == 1i32";
```
