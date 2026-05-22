# Spec Language Reference

This document describes the spec language that is implemented today. It covers only the language itself: where spec code may appear, which expressions are accepted, how binders work, and which forms are currently rejected.

The language appears in two places:

- directives written in spec comments, such as `//@ let`, `//@ req`, `//@ ens`, `//@ assert`, `//@ assume`, `//@ inv`, and `//@ lemma_name(...)`
- ghost item blocks written as `/*@ ... */` whose contents begin with `def`, `lem`, `unsafe lem`, `fn`, `unsafe fn`, `enum`, or `struct`

For each Rust source file, a sidecar file with the same path plus `.tsuno` is
also treated as ghost-item source. For example, if `src/foo.rs` is verified and
`src/foo.rs.tsuno` exists, the sidecar contents are interpreted as if they were
wrapped in `/*@ ... */` and inserted at the start of `src/foo.rs`.

When `cargo tsuno` is configured with an external spec root, the same rule is
applied using paths relative to the subject root. For example, with subject root
`prod-repo` and spec root `proof-repo/specs`, `prod-repo/src/foo.rs` reads
`proof-repo/specs/src/foo.rs.tsuno` as an additional ghost-item source. The
production Rust file does not need to contain any tsuno comments.

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
def add1(x: i32) -> i32 =
    x + 1i32
*/
```

Ghost item blocks can also be written with line comments, or by mixing line and block comments.

```rust
//@ lem trivial(n: Nat)
//@   req true
//@   ens true
//@ {}

/*@ lem also_trivial(n: Nat) */
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
expr as Ty
isize::MAX
*expr
-expr
!expr
lhs + rhs
lhs - rhs
lhs * rhs
lhs % rhs
lhs & rhs
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
3. cast           as
4. multiplicative *   %
5. additive       +   -
6. sequence concat ++
7. bitwise and    &
8. comparison     <   <=   >   >=
9. equality       ==   !=
10. conjunction   &&
11. disjunction   ||
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

def len(xs: List<i32>) -> i32 = ...
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

Integer expressions can be cast with `expr as Ty`, where `Ty` is an integer
spec type. A cast whose range check is statically false makes verification
fail. A cast whose range check is not statically provable is currently reported
as unsupported instead of being assumed. The builtin associated constant
`isize::MAX` is available as an `isize` value and is simplified for the target
pointer width.

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

struct Layout {
    size: usize,
    align: usize,
} where align != 0usize &&
    (align & (align - 1usize)) == 0usize &&
    size + align - 1usize <= (isize::MAX as usize);
```

The prelude also declares `def layout_of(ty: RustTy) -> Layout;` as an
uninterpreted pure function. Layout facts can be supplied by ordinary lemmas
whose bodies assume contradiction; for example, the prelude includes a lemma proving
`layout_of({type i32}) == Layout { size: 4usize, align: 4usize }`.

The prelude can also declare standalone contracts for Rust functions. A
standalone function contract is a ghost item of the form
`fn path::to::item<T>(...) -> ResultTy` or
`unsafe fn path::to::item<T>(...) -> ResultTy`, followed by ordinary `req`/`ens`
clauses and, for unsafe functions, raw `raw req`/`raw ens` clauses, and
terminated by `;` or followed by a standalone proof body. The parameter and result types use Rust type syntax, while
ordinary contract expressions see the corresponding spec model values.
Standalone contracts may target existing safe or unsafe Rust functions. If the
target function body also has inline contract directives, the duplicate
declaration is rejected. The old `extern fn` and `unsafe extern fn` ghost item
forms are not accepted.

```rust
/*@
unsafe fn core::intrinsics::read_via_copy<T>(ptr: *const T) -> T
  raw req *ptr |-?-> Option::<T>::Some(?old) * Own::<T>(old)
  raw ens *ptr |-?-> Option::<T>::Some(old)
  ens result == old
;
*/
```

A standalone proof body attaches function-body directives without writing them
inside the Rust function body. The body contains `at` blocks:

```rust
/*@
fn count_to(n: i32) -> ()
  req n >= 0i32
  ens true
{
  at stmt #0 {
    let initial = {n};
    assert initial == {n};
  }
  at loop #0 {
    inv 0i32 <= {x} && {x} <= {n};
  }
  at exit #0 {
    assert true;
  }
}
*/
```

Rules:

- `at stmt #N` attaches directives immediately before the Nth statement or tail expression visited in function-body order, including statements inside nested blocks
- `at loop #N` attaches to the Nth loop visited in function-body order and must contain exactly one `inv` directive
- `at exit #N` attaches directives immediately before the Nth return terminator
- `at stmt` and `at exit` blocks may contain `let`, `assert`, `assume`, `raw assert`, and lemma-call directives
- directive expressions inside `at` blocks use the same runtime syntax as inline body directives, so Rust locals are written as `{name}`
- a function body may not mix inline body directives with standalone proof-body directives

Enum variant selectors use `expr as Enum::Ctor` or
`expr as Enum::Ctor::<T, ...>`. The selector projects the payload of the named
variant without adding a runtime check or a tag assumption. If `expr` is not
that variant, the selected payload is unspecified, matching SMT datatype
selector semantics. Use `match` for ordinary safe destructuring.

Tuple-like variants expose tuple fields:

```rust
enum Maybe<T> {
    None,
    Some(T),
}

//@ assert (Maybe::<i32>::Some({x}) as Maybe::Some::<i32>).0 == {x};
```

Struct-like variants expose their declared field names. Internally, the payload
has the same shape as a generated spec struct named `Enum::Ctor`.

```rust
enum List<T> {
    Nil,
    Cons { head: T, tail: List<T> },
}

//@ assert (xs as List::Cons::<T>).head == h;
```

The enum name is required in selectors. `xs as Cons` is not valid. When explicit
type arguments are omitted, they are inferred from the selected expression's
enum type.

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
DeallocToken(base: usize, layout: Layout)
PointsTo(addr: usize, ty: RustTy, value: Option<T>)
```

`Provenance { base }` identifies the allocation that a pointer is derived from,
while `Ptr.addr` is the byte address accessed by the pointer. There is no
separate allocation identifier in the current model; allocation identity is
represented by the allocation's base address.

`DeallocToken(base, layout)` is a linear deallocation capability for
the allocation whose base address and deallocation layout are described by the
token. It is not a dereferenceability witness, and ordinary raw reads and writes
do not require it. It is intended to be consumed only by deallocation APIs.
The current token has an implicit global allocator; future versions may extend
the token with an explicit allocator argument, such as `Global`.

`PointsTo` is a typed-cell resource and a dereferenceability witness for that
typed cell. `PointsTo(addr, ty, Some(v))` entails:

- `addr` is non-null.
- `addr` is aligned for `layout(ty)`.
- the `layout(ty)` footprint at `addr` is live storage.
- `v` is valid for the same spec model type that the safe-state engine uses for
  the Rust type represented by `ty`.

For example, a raw pointer is modeled as `Ptr`, a shared reference as `Ref<T>`,
and a mutable reference as `Mut<T>` in both safe and unsafe states.
`PointsTo(addr, ty, None)` entails the same non-nullness, alignment, and live
storage facts, but the typed cell is not initialized as `ty`. The initial model
does not represent byte-level ownership or physical pointer-sized layouts
separately from typed cells.

Unsafe states must be resource-well-formed: if two `PointsTo` resources are
simultaneously present, their Rust layout footprints must not overlap. The
footprint of `PointsTo(addr, ty, _)` is the byte range
`addr..addr + layout(ty).size`, using rustc's layout for `ty`.

A raw pointer read `*p: T` requires
`PointsTo(p.addr, {type T}, Some(v))`, preserves that resource, and produces
`v`. A raw pointer assignment `*p = x` requires
`PointsTo(p.addr, {type T}, _)` and `Valid(T, x)`, and updates the resource to
`PointsTo(p.addr, {type T}, Some(x))`. Raw pointer assignment for types with
`Drop` is currently unsupported. Moving out through a raw pointer dereference is
also unsupported; `ptr::read` will be specified separately as an unsafe API.

The intended contract for a future typed deallocation API is:

```text
dealloc<T>(p)
requires:
  DeallocToken(p.addr, layout_of({type T}))
  * PointsTo(p.addr, {type T}, Option::None)
ensures:
  emp
```

The `PointsTo(..., Option::None)` precondition says that the typed cell is live
and uninitialized as `T`; the `DeallocToken` precondition says that the caller
owns the right to deallocate that allocation with the matching layout. Both
resources are consumed. `emp` is used here as the usual separation-logic empty
heap notation; in the current raw contract syntax this is represented by
omitting a `raw ens` clause.

The safe-to-unsafe bridge is explicit. `enter_unsafe` converts each live safe
local that currently has a safe model value to
`PointsTo(base, {type local_ty}, Some(value))`. If the local has been moved out
or otherwise has no safe model value, it creates no initialized typed cell for
that local. Stack and local allocations do not produce `DeallocToken` resources;
such tokens come from raw contracts, unsafe API specifications, or future
bridge rules for ownership-bearing heap values. `exit_unsafe` converts bridged
local resources back to the safe state:
`PointsTo(base, {type local_ty}, Some(value))` becomes the local's safe model
value, while a missing `PointsTo` or `PointsTo(..., None)` leaves the safe local
without an initialized model value. A `PointsTo` resource used for this
safe-state reflection is consumed. After all bridged locals have been reflected,
the unsafe heap must be empty; any remaining `PointsTo` or `DeallocToken`
resource is reported as an unsafe exit error. This rule prevents linear unsafe
resources from being silently discarded when control returns to safe code.
Reflection may use path-condition equalities, so a resource such as
`PointsTo(result.addr, {type T}, Some(v))` can be reflected to a bridged local
when the unsafe path condition proves `result.addr == base`.

Raw contracts may also mention `Own::<T>(v)`. `PointsTo` is a shallow typed
cell resource: it records that an address currently stores `Some(v)` or is
typed but uninitialized with `None`. `Own::<T>(v)` is the separate ownership
resource for the value `v` itself. The type argument to `Own` is a Rust type
annotation and is resolved against Rust type parameters and known Rust struct
definitions before verification. `Own` is always a linear raw resource. For
primitive scalar types, the prelude provides unsafe lemmas such as `own_i32` and
`drop_own_i32` to produce and consume the corresponding `Own` resource from
`emp`; those lemmas are the mechanism for treating primitive ownership as freely
available when a proof wants that convention. A fully initialized cell is
therefore modeled as both resources:

```rust
//@ raw req *p |-?-> Option::<T>::Some(?v) * Own::<T>(v);
```

This is intentionally conservative. User-defined `Own` unfolding rules are not
yet part of the language; `Own` can be carried, consumed, and produced by raw
contracts, but the verifier does not currently expand it into field ownership.
Raw pointer reads of non-copy ownership transfer `Own::<T>(v)` from the pointed
cell to the produced value; reads of primitive/copy ownership leave the `Own`
resource available. Raw pointer writes transfer ownership of the written value
back to the pointed cell. This makes contracts such as `write_via_move<T>`
express the movement of ownership separately from the shallow `PointsTo` cell
update.

Branching inside an unsafe block keeps separate unsafe states for the feasible
paths. Unsafe heap resources are not merged at unsafe control-flow joins.
Instead, each unsafe exit state is converted back to a safe state with
`exit_unsafe`, and the ordinary safe-state engine may merge those safe states at
the following safe control point. This makes path splitting inside unsafe blocks
visible: deeply nested unsafe branches can create multiple unsafe states before
control returns to safe code.

Currently supported unsafe code is single-threaded Rust for raw pointer reads
and writes, ordinary branches, ordinary reference construction, checked integer
arithmetic, and calls to ordinary safe Rust functions. An `unsafe fn` body is
verified by the unsafe engine even when it has no `raw req` or
`raw ens` clauses. A safe function call from unsafe code uses the same
contract behavior as safe code: the callee precondition is asserted, the callee
postcondition is assumed, and opaque calls produce a fresh result satisfying the
result type invariant. Unsafe function calls from unsafe code are supported when
the unsafe callee has a local function contract. Ordinary `req` and `ens`
clauses keep their path-condition meaning, and unsafe heap requirements are
written with `raw req` and `raw ens`.

```rust
unsafe fn write_i32(p: *mut i32)
//@ raw req *p |-?-> Option::Some(?old)
//@ raw ens *p |-?-> Option::Some(42i32) where old >= 0i32
{
    // ...
}
```

`raw req` and `raw ens` use the same raw-pattern syntax as
`raw assert`. They may be omitted independently. `//@ let` directives may
appear before `raw req`, as with ordinary function contracts. Raw function
contracts are supported only on `unsafe fn`.

When an unsafe function body is verified, each `raw req` materializes the
specified resources into the function's initial unsafe heap and assumes its
`where` condition. At each return, ordinary `ens` clauses are asserted, then each
`raw ens` is checked against the function's final unsafe heap. Raw
postcondition matching is exact: each raw pattern must match exactly one
set of heap resources after its `where` condition is applied. The matched
resources are consumed at return because no unsafe heap is reflected to a caller
during callee-body verification. After those postcondition resources and the
callee's own bridged local resources have been consumed, the final unsafe heap
must be empty.

At an unsafe call site, each `raw req` is checked against the caller's
unsafe heap and consumes exactly the matched resources. Each `raw ens`
materializes resources back into the caller heap after the call. If a
`raw ens` has a `where` clause, that boolean condition is also added to the
caller path condition after the call. The `result` variable is available in both
the raw pattern and the `where` clause of `raw ens`.

The same call-site rule is used for functions with standalone ghost contracts.
The verifier looks up the callee's Rust path, instantiates any Rust generic type
arguments into the ghost contract, checks ordinary and raw preconditions, and
then assumes ordinary and raw postconditions. Unsafe functions without either an
inline contract or a matching standalone contract are rejected.

Unsafe lemmas use the same raw contract model as unsafe functions. They are
declared as ghost items with `unsafe lem`, spec parameters, optional ordinary
`req` and `ens` clauses, and optional `raw req` and `raw ens` clauses:

```rust
/*@
unsafe lem keep_i32_cell(p: Ptr)
  raw req PointsTo(p.addr, {type i32}, Option::Some(?old))
  raw ens PointsTo(p.addr, {type i32}, Option::Some(?v)) where v == old
{
}
*/
```

An unsafe lemma body is verified. Its `raw req` clauses materialize the
initial unsafe heap, and its `raw ens` clauses are checked against the final
unsafe heap. After the lemma's `raw ens` clauses are consumed, its final
unsafe heap must be empty. Calling an unsafe lemma from unsafe code applies the
same raw contract behavior as an unsafe function call: raw preconditions are
consumed from the caller heap and raw postconditions are
materialized back into it. Unsafe lemma calls are supported inside both unsafe
blocks and unsafe function bodies.

Inside unsafe blocks and unsafe function bodies, ordinary `//@ let`,
`//@ assert`, `//@ assume`, and lemma-call directives are supported when they
only affect the symbolic path condition or the directive environment, as they do
in safe code. Unsafe code also supports raw assertions:

```rust
//@ raw assert PointsTo({p}.addr, {type i32}, Option::Some(42i32));
//@ raw assert PointsTo({p}.addr, {type i32}, Option::Some(?v)) where v > 0i32;
//@ raw assert *p |-?-> Option::Some(?v) where v > 0i32;
```

A raw assertion checks a `RawPattern`. The initial raw patterns
are `emp`,
`PointsTo(addr_expr, rust_ty_expr, option_value_expr)`,
the shorthand `*ptr |-?-> option_value_pattern`,
`DeallocToken(base_expr, layout_expr)`, and separating
conjunction `left * right`; parentheses may be used freely to group raw
patterns.
`emp` is the empty raw pattern: it matches without requiring any heap resource,
consumes no resource in `raw req` or `raw ens`, and materializes no resource.
It may be combined with other raw patterns as in `emp * R` or `R * emp`.
`*ptr |-?-> value` is accepted only when `ptr` is a Rust local, function
parameter, or allowed `result` binding whose type is a raw pointer `*const T` or
`*mut T`; it is desugared before unsafe execution to
`PointsTo({ptr}.addr, {type T}, value)`, so the unsafe engine only sees
`PointsTo`. If the pointer type cannot be inferred, the directive is rejected
before unsafe execution. The value expression for a `PointsTo` pattern is an
ordinary spec expression whose type is `Option<T>`, so option constructors are
written as prelude enum constructors such as `Option::Some(v)` and
`Option::None`.

The third argument of `PointsTo` is a value pattern. A pattern variable is
written `?name`; in `PointsTo(a, {type T}, ?v)`, `v` has type `Option<T>`, while
in `PointsTo(a, {type T}, Option::Some(?v))`, `v` has type `T`. Constructor
syntax in a value pattern is structural pattern syntax, so constructor arguments
may themselves contain pattern variables. Pattern variables are bound from left
to right, are visible in the optional `where` condition, and remain available to
later directives in the same directive environment.

`raw assert R where P` first enumerates matches of `R` against the current
unsafe heap, using `*` to require distinct matched atomic resources. It then
filters those matches by the boolean spec expression `P`; if the `where` clause
is omitted, `P` is `true`. The directive succeeds only when exactly one match
remains under the current path condition. If no matching resource remains,
verification fails; if multiple matches remain or a match is only
path-conditionally possible, the assertion is currently reported as unsupported.
Raw assertions do not consume resources, and no backtracking crosses a
directive boundary. Raw assertions are only supported inside unsafe blocks.

Loop invariants inside unsafe blocks are not supported. Loop contracts inside
unsafe code are not supported yet; existing loop prepass restrictions still
apply before unsafe execution. Aliasing, permissions, fractional permissions,
and user-defined heap predicates are not part of this initial unsafe model.

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
fields. A struct literal must name a declared spec struct. Rust structs used by
the verified program are also registered as same-shaped spec structs during the
prepass, so Rust struct field access and spec struct field access use the same
nominal struct model.

```rust
/*@
struct Foo {
    bar: isize,
    baz: bool,
}
*/

//@ assert (Foo { bar: 42isize, baz: true }).bar == 42isize;
```

Struct and enum declarations may end with a type invariant written as
`where <bool expr>;`. A struct invariant may refer to its fields by bare field
name. An enum invariant may refer to the constructed value as `self`.

```rust
/*@
struct Odd {
    n: Nat,
} where n % 2 == 1;

enum Small {
    One(Int),
} where (self as Small::One).0 < 10;
*/

//@ let odd = Odd { n: 3Nat };
//@ let small = Small::One(9);
```

When a spec value is introduced with `let`, the corresponding type invariant is
asserted. Where a value's spec type is used as an invariant, the user-written
type invariant is conjoined with the existing field and constructor invariant.

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

def len(xs: List<i32>) -> i32 =
    match xs {
        List::Nil => 0i32,
        List::Cons(_, xs0) => 1i32 + len(xs0),
    }

lem append_len(xs: List<i32>, ys: List<i32>)
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
- pure functions: `def name<T>(args...) -> Ty = expr`
- uninterpreted pure function declarations: `def name<T>(args...) -> Ty;`
- lemmas: `lem name<T>(args...) req <expr> ens <expr> { stmts }`
- unsafe lemmas:
  `unsafe lem name<T>(args...) req <expr> raw req <pattern> ens <expr> raw ens <pattern> { stmts }`

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
def len(xs: List<i32>) -> i32 =
    match xs {
        List::Nil => 0i32,
        List::Cons(_, xs0) => 1i32 + len(xs0),
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
