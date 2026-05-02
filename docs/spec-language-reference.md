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
- if a contract is present, it must contain at least one of `//@ req` or `//@ ens`
- a missing `//@ req` is treated as `//@ req true`, and a missing `//@ ens` is treated as `//@ ens true`
- a contract may contain at most one `//@ req` and at most one `//@ ens`
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

Spec expressions are written directly. In runtime specs (`req`, `ens`, `assert`, `assume`, `inv`, and runtime lemma calls), a bare identifier refers only to a visible spec binder. The only built-in bare name is `result` in `ens`. A Rust binding must be written as `{name}`. A Rust type value is written as `{type T}`.

```rust
//@ assert {x} == 1i32;
//@ assert *{r} == 1i32;
//@ assert {pair}.left == 1i32;
//@ assert {pair}.0 == 1i32;
//@ assert {p}.ty == {type i32};
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

Interpolation composes with the surrounding spec syntax. The content of `{...}` is either a single Rust binding name or `type` followed by a Rust type.

```text
{x}
*{r}
{pair}.0
{type i32}
{type T}
{type *const T}
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
43Nat
42usize
result
x
{x}
f(x, y)
Enum::Ctor(x, y)
Enum::<T>::Ctor(x)
StructName { field: value }
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
RustTy
Int
i8   i16   i32   i64   isize
u8   u16   u32   u64   usize
Seq<T>
Ref<T>
Mut<T>
Ptr
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

`Int` is an unbounded mathematical integer. Integer literals may be unsuffixed
or use one of the integer suffixes above. In an `Int` context, an unsuffixed
integer literal is interpreted as an `Int`; in a `Nat` context, it is interpreted
as a `Nat`. The `Nat` suffix makes this explicit.

```text
0
43Nat
1i32
42usize
18446744073709551615u64
```

Boolean literals are written as `true` and `false`. Boolean values can also be
produced by comparisons, equality, logical operators, and predicate calls.

Equality and inequality require matching spec types. Equality on `Ref<T>` and `Mut<T>` is currently rejected.

## 5. References, Fields, Tuples, and Sequences

The prelude declares the reference and pointer model types used for Rust
references and raw pointers.

```rust
enum Option<T> {
    None,
    Some(T),
}

struct Provenance {
    base: usize,
}

struct Ptr {
    addr: usize,
    prov: Option<Provenance>,
    ty: RustTy,
}

struct Ref<T> {
    deref: T,
    ptr: Ptr,
}

struct Mut<T> {
    cur: T,
    fin: T,
    ptr: Ptr,
}
```

`RustTy` is a builtin spec type used to represent Rust types as spec values.
Each Rust type has a corresponding `RustTy` value, produced with `{type ...}`.
For example, `{type i32}` denotes the model value for Rust `i32`, and `{type T}`
denotes the model value for the Rust type parameter `T` in the surrounding
Rust item. Distinct observed Rust type values are treated as distinct by the
solver.
`Provenance` currently records only the allocation base address; borrow tags for
Tree Borrows are not part of the model yet. Rust raw pointer types are modeled
as `Ptr`.
`Ref<T>` and `Mut<T>` values require `ptr.prov` to be `Some(_)`; raw `Ptr`
values may have no provenance because null, dangling, and integer-derived
pointers are representable.

Pointers created from Rust places carry a stable place-derived identity. Taking
`&x`, `&raw const x`, or `&raw mut x` gives a pointer whose `prov` is
`Some(Provenance { base: ... })`; taking a pointer to a field keeps the same
provenance base and uses `base + offset`, where field offsets come from
rustc's type layout query for the Rust type. Repeating a borrow of the same
place gives the same modeled `addr` and `prov`. Different live locals get
different allocation base addresses and non-overlapping address ranges.
Every live allocation has a distinct non-null base address, including
zero-sized allocations. This keeps allocation identity available for strict
provenance and pointer-identity reasoning even when the allocation has no
non-empty byte range. Allocation base addresses are constrained to satisfy the
Rust type's ABI alignment from rustc's layout query. Layout-dependent pointer
formation currently supports field projections, including fields below a
dereferenced reference or raw pointer; DST metadata and non-field projections
are not modeled yet.

Strict-provenance APIs can be used through ordinary local wrapper contracts.
For example:

```rust
fn ptr_eq_u8(lhs: *const u8, rhs: *const u8) -> bool
//@ req true
//@ ens result == ({lhs}.addr == {rhs}.addr)
{
    //@ assume false;
    std::ptr::eq(lhs, rhs)
}

fn null_u8() -> *const u8
//@ req true
//@ ens result.addr == 0usize && result.prov == Option::<Provenance>::None && result.ty == {type u8}
{
    //@ assume false;
    std::ptr::null::<u8>()
}
```

## 6. Unsafe Blocks

Unsafe blocks use an address-based heap model. Entering an unsafe block converts
the currently visible safe Rust state into unsafe heap resources, and leaving
the unsafe block converts the updated resources back into safe Rust state.

The initial unsafe heap model is address-based and has only two resource forms:

```text
Alloc(base: usize, size: usize, alignment: usize)
PointsTo(addr: usize, ty: RustTy, value: Option<T>)
```

`Alloc(base, size, alignment)` is keyed by `base`; there is no separate
allocation identifier. `Provenance { base }` identifies the allocation that a
pointer is derived from, while `Ptr.addr` is the byte address accessed by the
pointer. `Alloc` records the live allocation range and alignment for that base.

`PointsTo` is a typed-cell resource. `PointsTo(addr, ty, Some(v))` means that
`addr` is non-null, aligned for `ty`, and contains one initialized value valid
for the same spec model type that the safe-state engine uses for the Rust type
represented by `ty`. For example, a raw pointer is modeled as `Ptr`, a shared
reference as `Ref<T>`, and a mutable reference as `Mut<T>` in both safe and
unsafe states. `PointsTo(addr, ty, None)` means that the typed cell exists but
is not initialized. The initial model does not represent byte-level ownership or
physical pointer-sized layouts separately from typed cells.

Unsafe states must be resource-well-formed: if two `PointsTo` resources are
simultaneously present, their Rust layout footprints must not overlap. The
footprint of `PointsTo(addr, ty, _)` is the byte range
`addr..addr + layout(ty).size`, using rustc's layout for `ty`.

A raw pointer dereference of type `T` requires all of the following:

- `Ptr.ty == {type T}`.
- `Ptr.prov == Some(Provenance { base })`.
- `Alloc(base, size, alignment)` exists.
- `Ptr.addr..Ptr.addr + layout(T).size` is within `base..base + size`.
- `Ptr.addr` is non-null and aligned for `T`.
- `PointsTo(Ptr.addr, {type T}, Some(v))` exists for reads, and
  `PointsTo(Ptr.addr, {type T}, _)` exists for writes.

The safe-to-unsafe bridge is explicit. `enter_unsafe` converts each live safe
local allocation to `Alloc(base, size, alignment)` using rustc's layout size and
ABI alignment. If the local currently has a safe model value, it also creates
`PointsTo(base, {type local_ty}, Some(value))`; if the local has been moved out
or otherwise has no safe model value, it creates no initialized typed cell for
that local. `exit_unsafe` converts bridged local resources back to the safe
state: `PointsTo(base, {type local_ty}, Some(value))` becomes the local's safe
model value, while a missing `PointsTo` or `PointsTo(..., None)` leaves the safe
local without an initialized model value.

Branching inside an unsafe block keeps separate unsafe states for the feasible
paths. Unsafe heap resources are not merged at unsafe control-flow joins.
Instead, each unsafe exit state is converted back to a safe state with
`exit_unsafe`, and the ordinary safe-state engine may merge those safe states at
the following safe control point. This makes path splitting inside unsafe blocks
visible: deeply nested unsafe branches can create multiple unsafe states before
control returns to safe code.

Currently supported unsafe code is single-threaded Rust for raw pointer reads
and writes, ordinary branches inside unsafe blocks, ordinary reference
construction, checked integer arithmetic, and calls to ordinary safe Rust
functions. A safe function call inside an unsafe block uses the same
contract behavior as safe code: the callee precondition is asserted, the callee
postcondition is assumed, and opaque calls produce a fresh result satisfying the
result type invariant. Unsafe function calls inside unsafe blocks are not
supported. This support is for safe function calls only; unsafe API
heap/layout/value specifications are separate unsafe resources and are not part
of this initial model.

Inside unsafe blocks, ordinary `//@ let`, `//@ assert`, `//@ assume`, and
lemma-call directives are supported when they only affect the symbolic path
condition or the directive environment, as they do in safe code. Unsafe blocks
also support resource assertions:

```rust
//@ resource assert PointsTo({p}.addr, {type i32}, Option::Some(42i32)) * Alloc({p}.addr, 4usize, 4usize);
//@ resource assert PointsTo({p}.addr, {type i32}, Option::Some(?v)) where v > 0i32;
```

A resource assertion checks a `ResourcePattern`. The initial resource patterns
are `PointsTo(addr_expr, rust_ty_expr, option_value_expr)`,
`Alloc(base_expr, size_expr, alignment_expr)`, and separating conjunction
`left * right`; parentheses may be used freely to group resource patterns. The
value expression for a `PointsTo` pattern is an ordinary spec expression whose
type is `Option<T>`, so option constructors are written as prelude enum
constructors such as `Option::Some(v)` and `Option::None`.

The third argument of `PointsTo` is a value pattern. A pattern variable is
written `?name`; in `PointsTo(a, {type T}, ?v)`, `v` has type `Option<T>`, while
in `PointsTo(a, {type T}, Option::Some(?v))`, `v` has type `T`. Constructor
syntax in a value pattern is structural pattern syntax, so constructor arguments
may themselves contain pattern variables. Pattern variables are bound from left
to right, are visible in the optional `where` condition, and remain available to
later directives in the same directive environment.

`resource assert R where P` first enumerates matches of `R` against the current
unsafe heap, using `*` to require distinct matched atomic resources. It then
filters those matches by the boolean spec expression `P`; if the `where` clause
is omitted, `P` is `true`. The directive succeeds only when exactly one match
remains under the current path condition. If no matching resource remains,
verification fails; if multiple matches remain or a match is only
path-conditionally possible, the assertion is currently reported as unsupported.
Resource assertions do not consume resources, and no backtracking crosses a
directive boundary. Resource assertions are only supported inside unsafe blocks.

Loop invariants inside unsafe blocks are not supported. Loop contracts and
function contracts inside unsafe code are not supported yet; existing loop
prepass restrictions still apply before unsafe execution. Aliasing,
permissions, fractional permissions, and user-defined heap predicates are not
part of this initial unsafe model.

Shared references can be dereferenced with `*`. After type checking, `*r` for a
`Ref<T>` is desugared to `r.deref`.

```rust
//@ assert *{x} == {y};
```

Mutable references expose the current value through `*` and `.cur`, the final
value through `.fin`, and the modeled pointer through `.ptr`. After type
checking, `*r` for a `Mut<T>` is desugared to `r.cur`.

```rust
//@ let Old = *{xs};
//@ req true
//@ ens {xs}.fin == Old ++ [x]
```

Named field access works on structs.

```rust
//@ assert {pair}.left == 0i32;
```

Spec-side structs can be declared in ghost blocks and constructed with named
fields.

```rust
/*@
struct Foo {
    bar: isize,
    baz: bool,
}
*/

//@ assert (Foo { bar: 42isize, baz: true }).bar == 42isize;
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
- `struct`
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
