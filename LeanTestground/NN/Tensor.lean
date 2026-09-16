/-!
# Dense float tensors on top of `FloatArray`

Two primitives carry the whole language model:

* `Vec` -- a bare `FloatArray`, used for biases, norm gains and 1-D scratch.
* `Mat` -- a row-major `rows x cols` block of floats.

## Two performance rules, both learned the hard way

**1. Do not write `Float` literals inside a hot loop.** Lean does not
constant-fold them. A bare `0.0` in a loop body compiles to a fresh
`Float.ofScientific` call -- allocating `Nat`s and running the
scientific-notation decoder -- on *every iteration*. The generated C for a
one-line store loop looks like this, all of it inside the loop:

    v_5 = lean_unsigned_to_nat(10u);
    v_7 = l_Float_ofScientific(v_5, 1, ...);
    v_8 = lean_float_array_set(v_a, v_i, v_7);

Measured here that is a **20x** slowdown (6.8s vs 0.33s for a million stores).
Every constant below therefore comes from a top-level `def` -- see the note on
float constants just below, because a local `let` is *not* enough.

**2. Thread the output buffer linearly.** `FloatArray.set!` mutates in place
only while the array is uniquely referenced, so accumulators are passed as
arguments and returned, never captured from an enclosing scope.

With both rules applied the matmul kernels run at ~0.57 GFLOP/s single-threaded
and, importantly, at the *same* rate for every matrix size -- the sign that no
hidden copying is left.
-/

namespace TinyLM

/-! ## Float constants

These exist because a local binding is not a reliable hoist. Writing

    let zero := (0.0 : Float)

at the top of a function does *not* keep the constant out of the loop below it:
the compiler rematerialises cheap pure bindings at their use sites, and for a
float literal that means a `Float.ofScientific` call -- `Nat` allocations and
all -- on every iteration. This was visible in the generated C for `adamStep`,
whose inner loop rebuilt `1.0` a million times per training step and cost as
much as the entire batch gradient.

A top-level `def` compiles to a cached cell instead, which is a load. Use these
anywhere a constant is needed inside a loop. -/

def f0 : Float := 0.0
def f1 : Float := 1.0
def f2 : Float := 2.0
def f3 : Float := 3.0
def fHalf : Float := 0.5
def fTenth : Float := 0.1
/-- Stands in for negative infinity when seeding a running maximum. -/
def fNegBig : Float := -1e30

abbrev Vec := FloatArray

/-! ## Element access

`uget`/`uset` take a `USize` index plus a proof. Recovering that proof inside a
loop is not worth the trouble, so these wrappers discharge it with a dependent
`if` and fall back on the cold branch. The comparison costs a couple of
instructions, and `USize` arithmetic avoids `lean_nat_add`; together that is
worth about 1.25x over `get!`/`set!`. -/

@[inline] def fget (a : FloatArray) (i : USize) : Float :=
  if h : i.toNat < a.size then a.uget i h else f0

@[inline] def fset (a : FloatArray) (i : USize) (v : Float) : FloatArray :=
  if h : i.toNat < a.size then a.uset i v h else a

namespace Vec

/-- `n` copies of `v`. The fill value is a parameter, so the caller evaluates it
once rather than the loop evaluating it `n` times. -/
def const (n : Nat) (v : Float) : Vec := Id.run do
  let mut a := FloatArray.emptyWithCapacity n
  for _ in [0:n] do
    a := a.push v
  return a

/-- `n` zeroes. Routed through `const` so the `0.0` is built outside the loop. -/
def zeros (n : Nat) : Vec := const n f0

@[inline] def addAt (a : Vec) (i : Nat) (x : Float) : Vec :=
  a.set! i (a.get! i + x)

/-- Overwrite every entry with zero, keeping the allocation. -/
def zeroOut (a : Vec) : Vec := Id.run do
  let n := a.size
  let mut a := a
  for i in [0:n] do
    a := a.set! i f0
  return a

/-- Elementwise `a += b`. -/
def addInto (a b : Vec) : Vec := Id.run do
  let mut a := a
  for i in [0:a.size] do
    a := a.set! i (a.get! i + b.get! i)
  return a

end Vec

/-- A row-major matrix. The invariant `data.size = rows * cols` is maintained by
construction; carrying a proof of it through every kernel would cost far more
than it buys. -/
structure Mat where
  rows : Nat
  cols : Nat
  data : FloatArray
  deriving Inhabited

namespace Mat

def zeros (rows cols : Nat) : Mat := ⟨rows, cols, Vec.zeros (rows * cols)⟩

@[inline] def size (m : Mat) : Nat := m.rows * m.cols

/-! ### Matmul kernels

Three shapes are needed, one per position a gradient can arrive in:

| kernel      | computes        | used by                          |
|-------------|-----------------|----------------------------------|
| `mul`       | `A * B`         | forward `x @ W`                  |
| `mulTB`     | `A * Bt`        | backward to the input, `dY @ Wt` |
| `mulTAInto` | `out += At * B` | backward to the weight, `xt @ dY`|

All three loop in `i, p, j` order so the innermost stride is 1 over both the
right operand and the accumulator. -/

private partial def mulJ (bd : FloatArray) (av : Float) (iN pN j n : USize)
    (out : FloatArray) : FloatArray :=
  if j < n then
    let o := iN + j
    mulJ bd av iN pN (j + 1) n (fset out o (fget out o + av * fget bd (pN + j)))
  else out

private partial def mulP (ad bd : FloatArray) (iK iN p k n : USize)
    (out : FloatArray) : FloatArray :=
  if p < k then
    mulP ad bd iK iN (p + 1) k n (mulJ bd (fget ad (iK + p)) iN (p * n) 0 n out)
  else out

private partial def mulI (ad bd : FloatArray) (i m k n : USize)
    (out : FloatArray) : FloatArray :=
  if i < m then mulI ad bd (i + 1) m k n (mulP ad bd (i * k) (i * n) 0 k n out)
  else out

/-- `A * B` with `A : m x k` and `B : k x n`. -/
def mul (a b : Mat) : Mat :=
  ⟨a.rows, b.cols,
    mulI a.data b.data 0 a.rows.toUSize a.cols.toUSize b.cols.toUSize
      (Vec.zeros (a.rows * b.cols))⟩

private partial def tbDot (ad bd : FloatArray) (iK jK p k : USize) (acc : Float) : Float :=
  if p < k then tbDot ad bd iK jK (p + 1) k (acc + fget ad (iK + p) * fget bd (jK + p))
  else acc

private partial def tbJ (ad bd : FloatArray) (zero : Float) (iK iN j k n : USize)
    (out : FloatArray) : FloatArray :=
  if j < n then
    tbJ ad bd zero iK iN (j + 1) k n (fset out (iN + j) (tbDot ad bd iK (j * k) 0 k zero))
  else out

private partial def tbI (ad bd : FloatArray) (zero : Float) (i m k n : USize)
    (out : FloatArray) : FloatArray :=
  if i < m then tbI ad bd zero (i + 1) m k n (tbJ ad bd zero (i * k) (i * n) 0 k n out)
  else out

/-- `A * Bt` with `A : m x k` and `B : n x k`. -/
def mulTB (a b : Mat) : Mat :=
  ⟨a.rows, b.rows,
    tbI a.data b.data f0 0 a.rows.toUSize a.cols.toUSize b.rows.toUSize
      (Vec.zeros (a.rows * b.rows))⟩

private partial def taJ (bd : FloatArray) (av : Float) (pN iN j n : USize)
    (out : FloatArray) : FloatArray :=
  if j < n then
    let o := pN + j
    taJ bd av pN iN (j + 1) n (fset out o (fget out o + av * fget bd (iN + j)))
  else out

private partial def taP (ad bd : FloatArray) (iK iN p k n : USize)
    (out : FloatArray) : FloatArray :=
  if p < k then
    taP ad bd iK iN (p + 1) k n (taJ bd (fget ad (iK + p)) (p * n) iN 0 n out)
  else out

private partial def taI (ad bd : FloatArray) (i m k n : USize)
    (out : FloatArray) : FloatArray :=
  if i < m then taI ad bd (i + 1) m k n (taP ad bd (i * k) (i * n) 0 k n out) else out

/-- `out += At * B` with `A : m x k`, `B : m x n`, `out : k x n`. Accumulates, so
a whole mini-batch can be summed into one buffer. -/
def mulTAInto (out : Mat) (a b : Mat) : Mat :=
  ⟨out.rows, out.cols,
    taI a.data b.data 0 a.rows.toUSize a.cols.toUSize b.cols.toUSize out.data⟩

/-- Add a bias vector to every row. -/
def addRowVec (a : Mat) (v : Vec) : Mat := Id.run do
  let n := a.cols
  let mut d := a.data
  for i in [0:a.rows] do
    let iN := i * n
    for j in [0:n] do
      d := d.set! (iN + j) (d.get! (iN + j) + v.get! j)
  return { a with data := d }

/-- `out += column sums of A`; the bias gradient. -/
def sumRowsInto (out : Vec) (a : Mat) : Vec := Id.run do
  let n := a.cols
  let mut o := out
  for i in [0:a.rows] do
    let iN := i * n
    for j in [0:n] do
      o := o.addAt j (a.data.get! (iN + j))
  return o

/-- Elementwise `a += b`. -/
def addInto (a b : Mat) : Mat :=
  { a with data := Vec.addInto a.data b.data }

end Mat
end TinyLM
