import LeanTestground.BinaryAdder

set_option maxHeartbeats 1000000

/-!
# The symmetric subspace is a trap

Training the adder cell sometimes gets stuck at two wrong bits, and the states it gets stuck in
are always *tied*: all four hidden units carry the same incoming row and the same outgoing weight.
This file proves that no tied weights can ever work, for any values of the shared weights.

The reason is a collapse followed by a counting argument:

* **Collapse** (`sum_out_tied`). Four identical units compute the same hidden value, so the sum
  output is `σ (4 W σ(L) + b)` where `L = a₀x + a₁y + a₂c + a₃` is one affine form of the inputs.
  A 3→4→2 network with tied units is a 3→1→2 network.
* **Threshold** (`half_lt_sigma_iff`). The cell reports bit 1 exactly when its pre-activation is
  positive, and `σ` is strictly monotone (`sigma_strictMono`), so the reported sum bit is
  `L` compared against a fixed threshold: a linear threshold function of `(x, y, c)`.
* **Parity is not a halfplane.** The sum bit is `x ⊕ y ⊕ c`. Patterns `000`, `100`, `010`, `110`
  already rule that out: getting `100` right and `000` right forces the `x`-weight to one sign,
  getting `010` right and `110` right forces the other. Both pairs share the same `x`-weight,
  so the four cannot hold together.

The conclusion, `tied_not_certified`, is a statement about *all* tied weights, not about one
trained state: the whole subspace misses the adder. It is the one structural obstruction found in
this investigation — elsewhere the wrong-bit states that training visits are saddles with an
escape direction (see `PlateauCurvature.lean`), not minima.

The dynamical half of the trap is the second part of the file: the gradient at a tied state is
itself tied (`gradArr_tied`), and the grid step acts entrywise, so a run started inside the tied
set stays there forever (`stepArr_tied`). Together with the first half: descent from tied weights
never certifies, at any step, for any grid, learning rate and data (`tied_train_never_certifies`).

Not imported by the library. Check with `lake env lean LeanTestground/SymmetricTrap.lean`.
-/

namespace SymTrap

open BinAdd

/-! ## The activation is a strictly monotone threshold -/

theorem sigma_strictMono {z z' : ℚ} (h : z < z') : σ z < σ z' := by
  have hd : (0:ℚ) < 2 * (1 + |z|) := by positivity
  have hd' : (0:ℚ) < 2 * (1 + |z'|) := by positivity
  unfold BinAdd.σ
  have : z / (2 * (1 + |z|)) < z' / (2 * (1 + |z'|)) := by
    rw [div_lt_div_iff₀ hd hd']
    by_cases hz : (0:ℚ) ≤ z
    · have hz' : (0:ℚ) ≤ z' := le_of_lt (lt_of_le_of_lt hz h)
      rw [abs_of_nonneg hz, abs_of_nonneg hz']; nlinarith
    · have hzn : z < 0 := by push Not at hz; exact hz
      by_cases hz' : (0:ℚ) ≤ z'
      · rw [abs_of_neg hzn, abs_of_nonneg hz']; nlinarith
      · have : z' < 0 := by push Not at hz'; exact hz'
        rw [abs_of_neg hzn, abs_of_neg this]; nlinarith
  linarith

theorem sigma_lt_iff {z z' : ℚ} : σ z < σ z' ↔ z < z' := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rcases eq_or_lt_of_le hc with he | hlt
    · rw [he] at h; exact lt_irrefl _ h
    · exact absurd (sigma_strictMono hlt) (not_lt.mpr (le_of_lt h))
  · exact sigma_strictMono

theorem half_lt_sigma_iff (z : ℚ) : 1 / 2 < σ z ↔ 0 < z := by
  have hd : (0:ℚ) < 2 * (1 + |z|) := by positivity
  unfold BinAdd.σ
  constructor
  · intro h
    have : 0 < z / (2 * (1 + |z|)) := by linarith
    exact (div_pos_iff.mp this).elim (fun p => p.1) (fun p => absurd p.2 (not_lt.mpr hd.le))
  · intro h
    have : 0 < z / (2 * (1 + |z|)) := div_pos h hd
    linarith


/-! ## Evaluating the forward pass

`forwardWith id` is a fold over `List.finRange`, which reduces definitionally on the literal
lists, so these all hold by `rfl`. -/

theorem finRange4 : List.finRange 4 = [0, 1, 2, 3] := rfl
theorem finRange5 : List.finRange 5 = [0, 1, 2, 3, 4] := rfl



theorem z2_raw (θ : Matr 1 P ℚ) (v : Fin 4 → ℚ) (o : Fin 2) :
    (forward θ v).z2 o = 0 + w2 θ o 0 * BinAdd.σ ((forward θ v).z1 0)
      + w2 θ o 1 * BinAdd.σ ((forward θ v).z1 1)
      + w2 θ o 2 * BinAdd.σ ((forward θ v).z1 2)
      + w2 θ o 3 * BinAdd.σ ((forward θ v).z1 3) + w2 θ o 4 * 1 := rfl

theorem z1_raw (θ : Matr 1 P ℚ) (v : Fin 4 → ℚ) (h : Fin 4) :
    (forward θ v).z1 h = 0 + w1 θ h 0 * v 0 + w1 θ h 1 * v 1 + w1 θ h 2 * v 2 + w1 θ h 3 * v 3 := rfl

theorem out_raw (θ : Matr 1 P ℚ) (v : Fin 4 → ℚ) (o : Fin 2) :
    (forward θ v).out o = BinAdd.σ ((forward θ v).z2 o) := rfl

/-! ## The tied subspace -/

theorem inp0 (x y c : Bool) : input x y c 0 = boolQ x := rfl
theorem inp1 (x y c : Bool) : input x y c 1 = boolQ y := rfl
theorem inp2 (x y c : Bool) : input x y c 2 = boolQ c := rfl
theorem inp3 (x y c : Bool) : input x y c 3 = 1 := rfl

/-- The fully symmetric ("tied") set: all four hidden units share one incoming row, and each
output gives all four the same outgoing weight. Biases are free. -/
def Tied (θ : Matr 1 P ℚ) : Prop :=
  (∀ h i : Fin 4, w1 θ h i = w1 θ 0 i) ∧
  (∀ (o : Fin 2) (j : Fin 5), j.val < 4 → w2 θ o j = w2 θ o 0)

/-- The single affine form the tied network reduces to. -/
def lin (θ : Matr 1 P ℚ) (x y c : Bool) : ℚ :=
  w1 θ 0 0 * boolQ x + w1 θ 0 1 * boolQ y + w1 θ 0 2 * boolQ c + w1 θ 0 3

/-- On the tied set the sum output is `σ (4W σ(L) + b)` with `L` one affine form of the inputs:
four identical units act as a single unit. -/
theorem sum_out_tied {θ : Matr 1 P ℚ} (hT : Tied θ) (x y c : Bool) :
    (forward θ (input x y c)).out 0 =
      BinAdd.σ (4 * w2 θ 0 0 * BinAdd.σ (lin θ x y c) + w2 θ 0 4) := by
  obtain ⟨h1, h2⟩ := hT
  unfold lin
  rw [out_raw, z2_raw]
  simp only [z1_raw, h1, h2 0 1 (by decide), h2 0 2 (by decide), h2 0 3 (by decide),
    inp0, inp1, inp2, inp3]
  ring_nf

theorem cancel_pos {W u v : ℚ} (hW : 0 < W) (h : W * u < W * v) : u < v := by
  by_contra hc; push Not at hc; nlinarith

theorem cancel_neg {W u v : ℚ} (hW : W < 0) (h : W * u < W * v) : v < u := by
  by_contra hc; push Not at hc; nlinarith

/-- **No tied weights ever pass the certificate.** Four identical hidden units compute one
affine form of `(x, y, c)`, and the sum bit is then a threshold on that form; but the sum bit
is the parity of `x, y, c`, which no halfplane separates. Patterns `000`, `100`, `010`, `110`
alone force a contradiction: the first pair makes the `x`-weight positive, the second pair
makes it negative. -/
theorem tied_not_certified {θ : Matr 1 P ℚ} (hT : Tied θ) : certificate θ = false := by
  by_contra hc
  have hcert : certificate θ = true := by
    cases h : certificate θ
    · exact absurd h hc
    · rfl
  -- the sum bit is right on every pattern
  have bit : ∀ x y c : Bool,
      decide (1 / 2 < (forward θ (input x y c)).out 0) = xor (xor x y) c :=
    fun x y c => congrArg Prod.fst (cert_sound hcert x y c)
  have pos : ∀ x y c : Bool, xor (xor x y) c = true →
      0 < 4 * w2 θ 0 0 * BinAdd.σ (lin θ x y c) + w2 θ 0 4 := by
    intro x y c ht
    have hb := bit x y c
    rw [ht, sum_out_tied hT] at hb
    exact (half_lt_sigma_iff _).mp (of_decide_eq_true hb)
  have neg : ∀ x y c : Bool, xor (xor x y) c = false →
      4 * w2 θ 0 0 * BinAdd.σ (lin θ x y c) + w2 θ 0 4 ≤ 0 := by
    intro x y c ht
    have hb := bit x y c
    rw [ht, sum_out_tied hT] at hb
    exact not_lt.mp fun h => of_decide_eq_false hb ((half_lt_sigma_iff _).mpr h)
  have l000 : lin θ false false false = w1 θ 0 3 := by simp [lin, BinAdd.boolQ]
  have l100 : lin θ true false false = w1 θ 0 0 + w1 θ 0 3 := by
    simp [lin, BinAdd.boolQ]
  have l010 : lin θ false true false = w1 θ 0 1 + w1 θ 0 3 := by
    simp [lin, BinAdd.boolQ]
  have l110 : lin θ true true false = w1 θ 0 0 + (w1 θ 0 1 + w1 θ 0 3) := by
    simp [lin, BinAdd.boolQ]; ring
  have p100 := pos true false false (by decide)
  have p010 := pos false true false (by decide)
  have n000 := neg false false false (by decide)
  have n110 := neg true true false (by decide)
  rw [l100] at p100; rw [l010] at p010; rw [l000] at n000; rw [l110] at n110
  set A := w1 θ 0 0
  set B := w1 θ 0 1
  set D := w1 θ 0 3
  set W := w2 θ 0 0
  rcases lt_trichotomy W 0 with hW | hW | hW
  · have h4 : 4 * W < 0 := by linarith
    have e1 : 4 * W * BinAdd.σ D < 4 * W * BinAdd.σ (A + D) := by linarith
    have e2 : 4 * W * BinAdd.σ (A + (B + D)) < 4 * W * BinAdd.σ (B + D) := by linarith
    have s1 : A + D < D := sigma_lt_iff.mp (cancel_neg h4 e1)
    have s2 : B + D < A + (B + D) := sigma_lt_iff.mp (cancel_neg h4 e2)
    linarith
  · rw [hW] at p100 n000
    simp at p100 n000
    linarith
  · have h4 : 0 < 4 * W := by linarith
    have e1 : 4 * W * BinAdd.σ D < 4 * W * BinAdd.σ (A + D) := by linarith
    have e2 : 4 * W * BinAdd.σ (A + (B + D)) < 4 * W * BinAdd.σ (B + D) := by linarith
    have s1 : D < A + D := sigma_lt_iff.mp (cancel_pos h4 e1)
    have s2 : A + (B + D) < B + D := sigma_lt_iff.mp (cancel_pos h4 e2)
    linarith

/-- Restated: tied weights get some input wrong. So a tied network never satisfies the hypothesis
of `learned_adds`, and the 3→1→2 collapse can never be repaired by choosing the weights better. -/
theorem tied_wrong_somewhere {θ : Matr 1 P ℚ} (hT : Tied θ) :
    ∃ x y c : Bool, cellOf θ x y c ≠ fullAdder x y c := by
  by_contra hc
  push Not at hc
  have : certificate θ = true := by
    refine List.all_eq_true.mpr fun p _ => ?_
    simpa using hc (pattern p).1 (pattern p).2.1 (pattern p).2.2
  rw [tied_not_certified hT] at this
  exact Bool.false_ne_true this

/-! ## The tied set is not empty

`θsym` is the state the numerical search converged to: the minimum of the loss restricted to the
tied set (weights rounded to multiples of 1/10). It is critical there to ten digits, no random
direction within a ball of radius 10³ lowers the loss, and its two wrong bits are the sum bits of
patterns `000` and `111` — the floor the theorem above says every tied state is stuck at. -/
def θsym : Matr 1 P ℚ := fun _ j =>
  if j.val < 16 then ![-91452727/10000, -88574125/10000, -95367813/10000, 137332764/10000]
      ⟨j.val % 4, by omega⟩
  else if j.val < 20 then 6140/10000
  else if j.val = 20 then -12466/10000
  else if j.val < 25 then -15129327/10000
  else 20401010/10000

example : Tied θsym := by
  constructor
  · decide +kernel
  · decide +kernel

-- false: the certificate fails, as `tied_not_certified` says it must
#eval certificate θsym
-- the wrong bits: patterns 000 and 111, both sum bits
#eval (List.finRange 8).filterMap fun p =>
  let (x, y, c) := pattern p
  if cellOf θsym x y c == fullAdder x y c then none
  else some (x.toNat, y.toNat, c.toNat)

/-! ## The tie is preserved by training

`gradArr` folds eight per-pattern contributions into one array of 26 entries. Its loops run over
literal lists, so `simp` unfolds them structurally into `Array.modify` chains (`gradArr_fold`), and
each contribution splits into an output-weight half and an input-weight half. Tied weights make the
four hidden activations equal, so the output half adds the same number to all four of an output's
hidden weights; they make the four backpropagated deltas equal, so the input half adds the same row
to all four hidden rows. So the gradient at a tied state is tied, and since the grid step is applied
entrywise, the next state is tied again.
-/

theorem finRange2 : List.finRange 2 = [0, 1] := rfl
theorem finRange8 : List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

theorem getD_modify {α} (G : Array α) (d : α) (k i : ℕ) (f : α → α) (hi : i < G.size) :
    (G.modify k f).getD i d = if k = i then f (G.getD i d) else G.getD i d := by
  simp [Array.getD, hi, Array.getElem_modify]

/-- Unconditional form of `getD_modify`: the bound sits inside the `if`, so rewriting with it
never leaves a side goal for `simp` to discharge. -/
theorem getD_mod {α} (G : Array α) (d : α) (k i : ℕ) (f : α → α) :
    (G.modify k f).getD i d = if k = i ∧ i < G.size then f (G.getD i d) else G.getD i d := by
  by_cases hi : i < G.size
  · rw [getD_modify G d k i f hi]
    by_cases hk : k = i <;> simp [hk, hi]
  · have h2 : ¬ i < (G.modify k f).size := by rwa [Array.size_modify]
    simp [Array.getD, hi]

/-- The tie on a flat array of the 26 parameters: the four hidden rows agree, and each output's
four hidden weights agree. `d` is the default `getD` uses off the end. -/
def TiedD {α} (d : α) (G : Array α) : Prop :=
  (∀ h i : ℕ, h < 4 → i < 4 → G.getD (h * 4 + i) d = G.getD i d) ∧
  (∀ o j : ℕ, o < 2 → j < 4 → G.getD (16 + o * 5 + j) d = G.getD (16 + o * 5) d)

theorem tiedD_replicate {α} (d : α) (n : ℕ) : TiedD d (Array.replicate n d) := by
  have h : ∀ i : ℕ, (Array.replicate n d).getD i d = d := by
    intro i
    by_cases hi : i < n <;> simp [Array.getD, hi]
  exact ⟨fun _ _ _ _ => by rw [h, h], fun _ _ _ _ => by rw [h, h]⟩

/-- Tied weights give every hidden unit the same pre-activation. -/
theorem z1_tied {r : ℚ → ℚ} {θ : Matr 1 P ℚ} (hT : Tied θ) (v : Fin 4 → ℚ) (h : Fin 4) :
    (forwardWith r θ v).z1 h = (forwardWith r θ v).z1 0 := by
  have e : (fun (s : ℚ) (i : Fin 4) => s + w1 θ h i * v i)
      = (fun s i => s + w1 θ 0 i * v i) := by
    funext s i; rw [hT.1]
  simp only [forwardWith, e]

/-- Hence the same activation. -/
theorem u_tied {r : ℚ → ℚ} {θ : Matr 1 P ℚ} (hT : Tied θ) (v : Fin 4 → ℚ) (j : Fin 5)
    (hj : j.val < 4) : (forwardWith r θ v).u j = (forwardWith r θ v).u 0 := by
  fin_cases j
  · rfl
  · show r (BinAdd.σ ((forwardWith r θ v).z1 1)) = r (BinAdd.σ ((forwardWith r θ v).z1 0))
    rw [z1_tied hT]
  · show r (BinAdd.σ ((forwardWith r θ v).z1 2)) = r (BinAdd.σ ((forwardWith r θ v).z1 0))
    rw [z1_tied hT]
  · show r (BinAdd.σ ((forwardWith r θ v).z1 3)) = r (BinAdd.σ ((forwardWith r θ v).z1 0))
    rw [z1_tied hT]
  · exact absurd hj (by decide)

/-- The output-weight half of one pattern's update, written out. -/
def bodyO (r : ℚ → ℚ) (d2 : Fin 2 → ℚ) (u : Fin 5 → ℚ) (G : Array ℚ) : Array ℚ :=
  let g := G
  let g := g.modify 16 (· + r (d2 0 * u 0))
  let g := g.modify 17 (· + r (d2 0 * u 1))
  let g := g.modify 18 (· + r (d2 0 * u 2))
  let g := g.modify 19 (· + r (d2 0 * u 3))
  let g := g.modify 20 (· + r (d2 0 * u 4))
  let g := g.modify 21 (· + r (d2 1 * u 0))
  let g := g.modify 22 (· + r (d2 1 * u 1))
  let g := g.modify 23 (· + r (d2 1 * u 2))
  let g := g.modify 24 (· + r (d2 1 * u 3))
  let g := g.modify 25 (· + r (d2 1 * u 4))
  g

/-- The input-weight half. -/
def bodyI (d1 v : Fin 4 → ℚ) (G : Array ℚ) : Array ℚ :=
  let g := G
  let g := g.modify 0 (· + d1 0 * v 0)
  let g := g.modify 1 (· + d1 0 * v 1)
  let g := g.modify 2 (· + d1 0 * v 2)
  let g := g.modify 3 (· + d1 0 * v 3)
  let g := g.modify 4 (· + d1 1 * v 0)
  let g := g.modify 5 (· + d1 1 * v 1)
  let g := g.modify 6 (· + d1 1 * v 2)
  let g := g.modify 7 (· + d1 1 * v 3)
  let g := g.modify 8 (· + d1 2 * v 0)
  let g := g.modify 9 (· + d1 2 * v 1)
  let g := g.modify 10 (· + d1 2 * v 2)
  let g := g.modify 11 (· + d1 2 * v 3)
  let g := g.modify 12 (· + d1 3 * v 0)
  let g := g.modify 13 (· + d1 3 * v 1)
  let g := g.modify 14 (· + d1 3 * v 2)
  let g := g.modify 15 (· + d1 3 * v 3)
  g

theorem size_bodyO (r : ℚ → ℚ) (d2 : Fin 2 → ℚ) (u : Fin 5 → ℚ) (G : Array ℚ) :
    (bodyO r d2 u G).size = G.size := by
  simp only [bodyO, Array.size_modify]

theorem size_bodyI (d1 v : Fin 4 → ℚ) (G : Array ℚ) : (bodyI d1 v G).size = G.size := by
  simp only [bodyI, Array.size_modify]

/-- Equal activations ⇒ the output half keeps the tie. -/
theorem bodyO_tied {r : ℚ → ℚ} {d2 : Fin 2 → ℚ} {u : Fin 5 → ℚ} {G : Array ℚ}
    (hu : ∀ j : Fin 5, j.val < 4 → u j = u 0) (hG : TiedD 0 G) (hs : G.size = 26) :
    TiedD 0 (bodyO r d2 u G) := by
  have hu1 := hu 1 (by decide)
  have hu2 := hu 2 (by decide)
  have hu3 := hu 3 (by decide)
  refine ⟨fun h i hh hi => ?_, fun o j ho hj => ?_⟩
  · have h0 := hG.1 h i hh hi
    interval_cases h <;> interval_cases i <;>
      simp only [bodyO, getD_mod, Array.size_modify, hs, Nat.reduceLT, Nat.reduceEqDiff,
        Nat.reduceMul, Nat.reduceAdd, and_true, reduceIte] <;>
      exact h0
  · have h0 := hG.2 o j ho hj
    interval_cases o <;> interval_cases j <;>
      simp only [bodyO, getD_mod, Array.size_modify, hs, Nat.reduceLT, Nat.reduceEqDiff,
        Nat.reduceMul, Nat.reduceAdd, and_true, reduceIte] <;>
      simp only [h0, hu1, hu2, hu3]

/-- Equal backpropagated deltas ⇒ the input half keeps the tie. -/
theorem bodyI_tied {d1 v : Fin 4 → ℚ} {G : Array ℚ} (hd : ∀ h : Fin 4, d1 h = d1 0)
    (hG : TiedD 0 G) (hs : G.size = 26) : TiedD 0 (bodyI d1 v G) := by
  have h1 := hd 1
  have h2 := hd 2
  have h3 := hd 3
  refine ⟨fun h i hh hi => ?_, fun o j ho hj => ?_⟩
  · have h0 := hG.1 h i hh hi
    interval_cases h <;> interval_cases i <;>
      simp only [bodyI, getD_mod, Array.size_modify, hs, Nat.reduceLT, Nat.reduceEqDiff,
        Nat.reduceMul, Nat.reduceAdd, and_true, reduceIte] <;>
      simp only [h0, h1, h2, h3]
  · have h0 := hG.2 o j ho hj
    interval_cases o <;> interval_cases j <;>
      simp only [bodyI, getD_mod, Array.size_modify, hs, Nat.reduceLT, Nat.reduceEqDiff,
        Nat.reduceMul, Nat.reduceAdd, and_true, reduceIte] <;>
      exact h0

/-! ### One pattern's contribution

Named pieces, so that the tie proofs never have to unify against a large term. -/

/-- Pattern `p`'s input vector. -/
def pv (p : Fin 8) : Fin 4 → ℚ := input (pattern p).1 (pattern p).2.1 (pattern p).2.2

/-- Pattern `p`'s target. -/
def pt (p : Fin 8) : Bool × Bool := fullAdder (pattern p).1 (pattern p).2.1 (pattern p).2.2

/-- The two output deltas, `count * (out - target)`. -/
def pd2 (r : ℚ → ℚ) (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) (p : Fin 8) : Fin 2 → ℚ :=
  ![r ((cnt p : ℚ) * ((forwardWith r θ (pv p)).out 0 - boolQ (pt p).1)),
    r ((cnt p : ℚ) * ((forwardWith r θ (pv p)).out 1 - boolQ (pt p).2))]

/-- The four hidden deltas, backpropagated through the output weights. -/
def pd1 (r : ℚ → ℚ) (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) (p : Fin 8) : Fin 4 → ℚ := fun h =>
  r ((pd2 r cnt θ p 0 * w2 θ 0 h.castSucc + pd2 r cnt θ p 1 * w2 θ 1 h.castSucc)
      * σ' ((forwardWith r θ (pv p)).z1 h))

/-- One pattern's contribution to `gradArr`, as the two halves. -/
def gBody (r : ℚ → ℚ) (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) (p : Fin 8) (G : Array ℚ) : Array ℚ :=
  bodyI (pd1 r cnt θ p) (pv p) (bodyO r (pd2 r cnt θ p) (forwardWith r θ (pv p)).u G)

/-- The gradient loop is eight contributions folded together. -/
theorem gradArr_fold (r : ℚ → ℚ) (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) :
    gradArr r cnt θ =
      (List.finRange 8).foldl (fun G p => gBody r cnt θ p G) (Array.replicate P 0) := by
  simp only [gradArr, gBody, pv, pt, pd1, pd2, bodyO, bodyI, Id.run, finRange2, finRange4,
    finRange5, finRange8, List.forIn_cons, List.forIn_nil, List.foldl_cons, List.foldl_nil]
  rfl

/-- At a tied state every hidden unit gets the same backpropagated delta. -/
theorem pd1_tied {r : ℚ → ℚ} {cnt : Fin 8 → ℕ} {θ : Matr 1 P ℚ} (hT : Tied θ) (p : Fin 8)
    (h : Fin 4) : pd1 r cnt θ p h = pd1 r cnt θ p 0 := by
  simp only [pd1]
  rw [z1_tied hT, hT.2 0 h.castSucc (by simp),
    hT.2 1 h.castSucc (by simp), hT.2 0 (0 : Fin 4).castSucc (by decide),
    hT.2 1 (0 : Fin 4).castSucc (by decide)]

/-- At a tied state, one pattern's contribution keeps the tie (and the size). -/
theorem gBody_step {r : ℚ → ℚ} {cnt : Fin 8 → ℕ} {θ : Matr 1 P ℚ} (hT : Tied θ) (p : Fin 8)
    {G : Array ℚ} (h : TiedD 0 G ∧ G.size = 26) :
    TiedD 0 (gBody r cnt θ p G) ∧ (gBody r cnt θ p G).size = 26 := by
  obtain ⟨hG, hs⟩ := h
  have hO : TiedD 0 (bodyO r (pd2 r cnt θ p) (forwardWith r θ (pv p)).u G) :=
    bodyO_tied (fun j hj => u_tied hT (pv p) j hj) hG hs
  have hsO : (bodyO r (pd2 r cnt θ p) (forwardWith r θ (pv p)).u G).size = 26 := by
    rw [size_bodyO]; exact hs
  exact ⟨bodyI_tied (pd1_tied hT p) hO hsO, by rw [gBody, size_bodyI, size_bodyO]; exact hs⟩

/-- **The gradient at a tied state is tied.** -/
theorem gradArr_tied {r : ℚ → ℚ} {cnt : Fin 8 → ℕ} {θ : Matr 1 P ℚ} (hT : Tied θ) :
    TiedD 0 (gradArr r cnt θ) := by
  rw [gradArr_fold, finRange8]
  simp only [List.foldl_cons, List.foldl_nil]
  exact (gBody_step hT 7 (gBody_step hT 6 (gBody_step hT 5 (gBody_step hT 4
    (gBody_step hT 3 (gBody_step hT 2 (gBody_step hT 1 (gBody_step hT 0
      ⟨tiedD_replicate 0 P, by simp⟩)))))))).1

/-! ### From the gradient to the training sequence -/

theorem getD_ofFn_nat {α} {n : ℕ} (f : Fin n → α) (k : ℕ) (hk : k < n) (d : α) :
    (Array.ofFn f).getD k d = f ⟨k, hk⟩ := by
  simp [Array.getD, Array.getElem_ofFn, hk]

/-- A tied array of grid indices embeds to tied weights. -/
theorem tied_of_tiedD {g : Grid} {a : Array ℕ} (ha : TiedD 0 a) :
    Tied (g.embedM (ofArr g a)) := by
  have key : ∀ j k : ℕ, a.getD j 0 = a.getD k 0 → ∀ (hj : j < P) (hk : k < P),
      g.embedM (ofArr g a) 0 ⟨j, hj⟩ = g.embedM (ofArr g a) 0 ⟨k, hk⟩ := by
    intro j k h hj hk
    show g.embed (ofArr g a 0 ⟨j, hj⟩) = g.embed (ofArr g a 0 ⟨k, hk⟩)
    congr 1
    exact Fin.ext (by show min g.k (a.getD j 0) = min g.k (a.getD k 0); rw [h])
  constructor
  · intro h i
    refine key _ _ ?_ _ _
    have := ha.1 h.val i.val h.isLt i.isLt
    simpa using this
  · intro o j hj
    refine key _ _ ?_ _ _
    have := ha.2 o.val j.val o.isLt hj
    simpa using this

/-- One grid step of a tied state is tied: the step is applied entrywise, and equal entries with
equal gradients stay equal. -/
theorem stepCore_tied {g : Grid} {η : ℚ} {a : Array ℕ} {G : Array ℚ}
    (ha : TiedD 0 a) (hG : TiedD 0 G) : TiedD 0 (stepCore g η a G) := by
  have key : ∀ j k : ℕ, ∀ (hj : j < P) (hk : k < P), a.getD j 0 = a.getD k 0 →
      G.getD j 0 = G.getD k 0 →
      (stepCore g η a G).getD j 0 = (stepCore g η a G).getD k 0 := by
    intro j k hj hk hA hG'
    rw [stepCore, getD_ofFn_nat _ _ hj, getD_ofFn_nat _ _ hk]
    have : ofArr g a 0 ⟨j, hj⟩ = ofArr g a 0 ⟨k, hk⟩ :=
      Fin.ext (by show min g.k (a.getD j 0) = min g.k (a.getD k 0); rw [hA])
    rw [this, hG']
  refine ⟨fun h i hh hi => ?_, fun o j ho hj => ?_⟩
  · exact key _ _ (by simp only [P]; omega) (by simp only [P]; omega)
      (ha.1 h i hh hi) (hG.1 h i hh hi)
  · exact key _ _ (by simp only [P]; omega) (by simp only [P]; omega)
      (ha.2 o j ho hj) (hG.2 o j ho hj)

/-- **Training cannot leave the tied set.** -/
theorem stepArr_tied {g : Grid} {η : ℚ} {cnt : Fin 8 → ℕ} {a : Array ℕ} (ha : TiedD 0 a) :
    TiedD 0 (stepArr g η cnt a) :=
  stepCore_tied ha (gradArr_tied (tied_of_tiedD ha))

/-- Every state of a run started tied is tied. -/
theorem iterf_stepArr_tied {g : Grid} {η : ℚ} {cnt : Fin 8 → ℕ} {a : Array ℕ}
    (ha : TiedD 0 a) (t : ℕ) : TiedD 0 (iterf t (stepArr g η cnt) a) := by
  induction t with
  | zero => exact ha
  | succ t ih => rw [iterf_step_eqn]; exact stepArr_tied ih

/-- **The dynamical trap.** Gradient descent on the grid, started from tied weights, never passes
the certificate — at any step, and for any grid, learning rate and data. Both halves are needed:
`stepArr_tied` says the run can never leave the tied set, and `tied_not_certified` says nothing in
that set computes the adder. -/
theorem tied_train_never_certifies {g : Grid} {η : ℚ} {cnt : Fin 8 → ℕ} {a : Array ℕ}
    (ha : TiedD 0 a) (t : ℕ) :
    certificate (g.embedM (train g η (grad cnt) (ofArr g a) t)) = false := by
  rw [← iterf_stepArr]
  exact tied_not_certified (tied_of_tiedD (iterf_stepArr_tied ha t))

theorem getD_replicate_lt {α} (d x : α) {n k : ℕ} (h : k < n) :
    (Array.replicate n x).getD k d = x := by simp [Array.getD, h]

/-- Any constant array of grid indices is tied. -/
theorem tiedD_replicate_const {α} (d x : α) {n : ℕ} (hn : P ≤ n) :
    TiedD d (Array.replicate n x) := by
  refine ⟨fun h i hh hi => ?_, fun o j ho hj => ?_⟩ <;>
    rw [getD_replicate_lt d x (by simp only [P] at hn; omega),
        getD_replicate_lt d x (by simp only [P] at hn; omega)]

/-- Concrete instance: the constant starts of the sweeps (`zeros`, `const`) can never learn,
however long they are trained and however fine the grid. -/
theorem const_train_never_certifies (g : Grid) (η : ℚ) (cnt : Fin 8 → ℕ) (k t : ℕ) :
    certificate (g.embedM (train g η (grad cnt) (ofArr g (Array.replicate P k)) t)) = false :=
  tied_train_never_certifies (tiedD_replicate_const 0 k le_rfl) t

/-- The same run, stated on inputs: at every step some input is added wrongly. -/
theorem tied_train_wrong {g : Grid} {η : ℚ} {cnt : Fin 8 → ℕ} {a : Array ℕ}
    (ha : TiedD 0 a) (t : ℕ) : ∃ x y c : Bool,
      cellOf (g.embedM (train g η (grad cnt) (ofArr g a) t)) x y c ≠ fullAdder x y c := by
  rw [← iterf_stepArr]
  exact tied_wrong_somewhere (tied_of_tiedD (iterf_stepArr_tied ha t))

end SymTrap

#print axioms SymTrap.gradArr_tied
#print axioms SymTrap.tied_train_never_certifies
#print axioms SymTrap.tied_not_certified
#print axioms SymTrap.tied_wrong_somewhere
