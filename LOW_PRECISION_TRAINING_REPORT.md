# Low-precision training in Lean: precision, stalls, and a certified adder

Two Lean modules that make "more weight precision gives better learning" precise, followed
by a network trained on u32 addition with weights on a grid of fractions, then proved correct
on every input.

| Module | What it contains |
|---|---|
| [`LeanTestground/Quantization.lean`](LeanTestground/Quantization.lean) | Float formats as grids of rationals; a derivative defined without limits; loss-decrease, error-floor and stall theorems over a `Seqv` |
| [`LeanTestground/BinaryAdder.lean`](LeanTestground/BinaryAdder.lean) | A grid-weight network trained to add u32; a certificate check that implies correctness on all 2⁶⁴ input pairs; the trained weights with that proof |
| [`LeanTestground/BinaryAdderRun.lean`](LeanTestground/BinaryAdderRun.lean) | Training experiments (not imported by the library) |

Every theorem named below is proved with no `sorry`, using only `propext`,
`Classical.choice` and `Quot.sound`.

---

## 1. The starting question

> Floats are bounded fractions and fit into u32. Can differentiability on floats be moved
> over to u32? JAX refuses to differentiate integer functions.

The answer came in stages, and user corrections changed the framing twice.

**First attempt, discarded.** I modelled floats as an approximation of ℝ. The user objected
that computer floats are not reals, and that `hmor2_exists` moves *operations*. Both points
hold. Everything below uses **ℚ and finite grids only**.

**Where it ended up.**

- **Transport has a direction.** A grid `Fin (k+1)` and ℚ form a `wmap` (`embed`, `round`,
  with `round ∘ embed = id`).
  - Grid → ℚ: `hmor2_exists` moves a grid operation onto ℚ, and `hmor2` holds **exactly**
    (`transportOp_hmor2`).
  - ℚ → grid: this is what low-precision kernels do. The rounded operation is only an
    **approximate** homomorphism, off by at most half a grid step (`approx_hmor2`).
- **Differentiability does not need limits.** `SmoothWith ℓ grad L` says `grad` is a
  function and the first-order Taylor error is at most `L/2·‖d‖²`. That is an operation plus
  an inequality, so it makes sense on bounded fractions. This is the sense in which fp8 gets
  "a derivative": the rounded gradient satisfies the same inequality plus an error set by
  the grid spacing.
- **This is why fp8-e5m2 trains.** The backward pass is an operation that can be moved onto
  the grid. What gets weaker is the *guarantee* that it predicts loss changes, and it weakens
  by an amount set by the grid spacing.

## 2. The precision theorems (`Quantization.lean`)

Training is a `Seqv`: `train g η gradQ W₀ t = iterf t (step …) W₀`, the same pattern as
`clatz_seqv`. One `step` is a gradient step followed by `round`.

| Theorem | Statement (informally) |
|---|---|
| `descent_step` | `loss(t+1) ≤ loss(t) − η/4·‖∇ℓ‖² + floorC`, where `floorC = (1/η + L)·nm·(s/2 + η·εg)²` |
| `loss_decreases` | loss strictly drops at step `t` whenever `η/4·‖∇ℓ‖² > floorC` |
| `loss_floor` | summed over `T` steps: `η/4·Σ‖∇ℓ‖² ≤ ℓ₀ − ℓmin + T·floorC` |
| `symGrid_half_antitone`, `symGrid_half_bits_small` | rounding error `R/k` shrinks with `k` and goes to 0 as bits are added |
| `stall`, `stall_forever` | if every update is under half a grid step, the weights never move again |

Here `s` is the grid spacing, `η` the learning rate, `L` the curvature bound, `n·m` the
number of weights, and `εg` how far the computed gradient may be from the true one.

**Insight 1: "loss decreases at every step" is false at fixed precision.** The best true
statement is conditional: loss decreases while the gradient is large compared with the grid
spacing, and the spacing sets an error floor that vanishes as precision grows. `stall_forever`
proves the condition can't be dropped. On the 5-point grid `{-1, -½, 0, ½, 1}` with target
1/10, training freezes at loss 1/100 from the first step.

**Insight 2: monotone in bits, not in `k`.** The worst-case rounding error `R/k` does shrink
with every extra point (`symGrid_half_antitone`). The *best loss the grid can reach* need not:
a grid of `k` points is generally not contained in the grid of `k+1` points, so some weight
settings are lost. Doubling (`k = 2^b`) nests the grids, so best loss is monotone in bits.
Clean "more is better" statements about what a grid can represent should be phrased in bits.

**Insight 3: f32 is affected too, at a threshold that scales with the weight.** f32 is not
evenly spaced, but each exponent range [2ᵉ, 2ᵉ⁺¹) holds 2²³ evenly spaced values. That is
exactly a `Grid`, so the theorems apply to a weight that stays inside one range. An update
vanishes when `|η·g| ≲ |w|·2⁻²⁴ ≈ 6·10⁻⁸·|w|`. At w = 1.0, any update below about 6·10⁻⁸ is
lost. This is why mixed-precision training keeps f32 master weights. For f64, as used by
`FloatArray` in `LeanTestground/NN`, the threshold is about 1.1·10⁻¹⁶·|w|. Stochastic
rounding removes the stall by making rounding correct on average.

## 3. The certified binary adder (`BinaryAdder.lean`)

**Task.** Learn u32 addition (wrapping at 2³²) with a network whose weights are fractions
on a `Grid`.

**Design.**

1. **What's proved about addition.** Adding two u32 means running a full adder over the 32
   bits, carry first bit to last. `runAdder` does this, producing sum bits as a `Seqv`.
   `serial_correct` proves that any cell equal to `fullAdder` gives exactly `a + b` for
   every pair of u32.
2. **The cell.** 3 inputs (x, y, carry in), 4 hidden units and 2 outputs (sum, carry out),
   with the rational sigmoid `σ z = 1/2 + z/(2(1+|z|))`. Its 26 weights form one
   `Matr 1 26`, so `step`/`train` from `Quantization.lean` apply unchanged.
3. **Data.** 64 random u32 pairs give 2048 bit positions. Each position becomes one
   (x, y, carry) example with the true carry supplied, so training is not recurrent. Only 8
   patterns exist, so the data enters as their counts.
4. **Gradient.** Backpropagation computed in fixed point: every intermediate is rounded to
   multiples of 2⁻²⁰. This is the `gradQ` of `Quantization.lean`.
5. **Certificate.** When the network runs, its outputs are cut off at 1/2, so the carry fed
   back is always a bit and the cell only ever sees the 8 patterns. `learned_adds`:
   `certificate θ = true → ∀ a b : UInt32, runAdder (cellOf θ) a b = a + b`.

**Insight 4: rounding the internal state back to bits turns an infinite check into a finite
one.** The network is trained on 2048 examples and checked on 8 patterns, yet the proof
covers all 2⁶⁴ input pairs. Generalisation is *proved*, not estimated. It works because
cutting the output off at 1/2 rounds the carry back onto a finite set: the same rounding
that causes stalls in section 2 is what makes verification finite here.

**Result.** From random starting weights, on a grid with range [-32, 32] and step 1/64,
with η = 1/512, the certificate passes at **step 825**. The weights are stored as `learned`
(grid indices). `learned_certified` is checked by the kernel (`decide +kernel`), and
`trained_net_adds` states that the trained network adds every pair of u32.
`BinaryAdderRun.lean` re-runs training and confirms it reproduces `learned`.

## 4. Experiments: grid spacing versus outcome

Same data, same seed, range [-32, 32], η = 1/512, starting weights within ±0.5. Only the
grid spacing changes.

| Grid step | Outcome | Squared error at the end |
|---|---|---|
| 1/64 | **certificate passes at step 825** | 0.012 |
| 1/8 | stopped at a fixed point at step 150 (`stall_of_fixed`) | 0.098 |
| 1/2 | alternates between two weight settings for all 2000 steps | 0.2057 / 0.2079 |

Squared-error curve for the 1/64 grid: 0.262 → 0.101 (step 50) → a long plateau near 0.04
(steps 300–775) → 0.026 (800) → 0.012 (825, certified). The network finds the solution
suddenly, after a plateau.

**Insight 5: representable is not the same as trainable.** The step-1/2 grid *does* contain
a correct adder. Hand-built weights, all multiples of 1/2 in [-32, 32], pass the certificate:
hidden unit `k` fires when `x + y + c ≥ k` (`z = 8(x+y+c) − 8k + 4`), the sum is
`h1 − h2 + h3`, and the carry is `h2`. `handCoarse_certified` / `handCoarse_adds` in
`BinaryAdderRun.lean` prove it. Their squared error is ≈ 0.0153, close to the fine grid's
0.012, while training on that same grid cycled around 0.206. Precision has two separate
effects: whether a solution **exists** on the grid, and whether **training can reach it**.
Here the coarse grid passes the first and fails the second. The theorems in section 2
describe the second effect: coarse spacing raises the stall threshold and the error floor.

**Insight 6: coarse grids fail in two different ways.** The 1/8 grid reaches a fixed point,
which `stall_of_fixed` covers: once a step leaves the weights unchanged, `train` is constant
forever. The 1/2 grid falls into a **period-2 cycle**: the step overshoots and rounds back.
No theorem in the file covers cycles yet.

**Caveat.** This is one seed per grid, and the random starting weights differ between grids.
The table illustrates the effect; it doesn't measure it.

## 5. What went wrong along the way, and what it taught

| Symptom | Cause | Fix |
|---|---|---|
| All grids stuck around squared error 0.10–0.26 | squared error on a saturating sigmoid: the `σ'` factor makes the gradient vanish on a plateau, so `η·g` falls below half a step — `stall` in practice | output gradient `out − target` (the analogue of sigmoid with cross-entropy; still an exact gradient of a well-defined loss) |
| Weights clamped at ±8 | cross-entropy-style training keeps growing the margins | range widened to [-32, 32] |
| 20 training steps took over 10 minutes | weights stored as `Matrix` closures: each step re-evaluated all previous steps, growing exponentially | training loop on `Array ℕ`, proved equal to `train` (`iterf_stepArr`) |
| Exact ℚ gradients hundreds of digits long | summing over 8 patterns multiplies unrelated denominators together | fixed-point gradient (2⁻²⁰): a concrete instance of `gradQ` |
| `simp` looping, `congr` timeouts | unfolding `Array.ofFn`, `getD` | a small lemma `getD_ofFn` plus direct `rw` |
| `sq` / `inner` ambiguous | clash with Mathlib's `sq` lemma and `Inner.inner` | renamed to `msq` / `minner` |

**Insight 7: the rounding step helps as well as hurts.** Keeping weights on a grid is what makes
exact rational training possible at all. Weights never accumulate large denominators, and
the fixed-point gradient does the same for intermediate values. Precision limits cause stalls,
but they also keep the computation finite.

## 6. Gaps and next steps

- **Assumptions left as hypotheses.** `InRange` (updates stay inside the grid's range; the
  1/64 run did clamp one weight at +32, so the descent bounds don't apply to it) and `hgQ`
  (the gradient error bound `εg`). An explicit `εg` for the 2⁻²⁰ fixed-point gradient is not
  proved.
- **Training is not linked to `learned` by a theorem.** The weights are pasted in, and the
  match is checked at run time only.
- **Cycles.** A theorem that recognises period-p cycles would cover the 1/2 grid, in the same
  way `stall_of_fixed` covers fixed points.
- **The real IEEE layout.** Generalise `Grid` to an increasing `embed` whose spacing changes
  from point to point, so `stall` covers f32/fp8 exactly, with the gap changing at each
  power of 2.
- **Stochastic rounding.** An expected-value version of `descent_step` where the floor term
  becomes a variance term.
- **Several seeds per grid step**, to turn section 4's table into a measurement.
- **Build time.** `import Mathlib` made rebuilds slow (about 16 minutes for `Basic.lean`,
  about 9 for `Quantization.lean`). Narrowing `Quantization.lean` to
  `import Mathlib.Data.Matrix.Basic` cut its build to 18 s, and `BinaryAdder.lean` builds in
  21 s. `Basic.lean` still imports `Mathlib.Tactic` and is the remaining slow step.

## Reproducing

```bash
lake build LeanTestground
lake env lean LeanTestground/BinaryAdderRun.lean
```

The second command re-runs the three training experiments (about 3 minutes) and prints the
loss curves, outcomes and certificates.
