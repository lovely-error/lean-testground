import LeanTestground.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Low-precision training as transported operations

Computer floats are bounded fractions. We model a float format as a finite grid of
rationals indexed by `Fin (k+1)`, related to `ℚ` by a `wmap` (embed / round).

* `hmor2_exists` moves grid operations onto `ℚ` exactly; rounded `ℚ` operations on the
  grid are only approximate homomorphisms (`approx_hmor2`).
* Differentiability is expressed by operations plus an inequality (`SmoothWith`), so it
  makes sense over `ℚ` with no limits.
* Training is a `Seqv` of grid matrices. Loss provably decreases while the gradient
  dominates the grid spacing (`loss_decreases`), the stationarity floor shrinks with the
  spacing (`loss_floor`, `symGrid_half_antitone`), and below the threshold training
  stalls (`stall`).
-/

@[reducible]
def Matr (n m) (T) := Matrix (Fin n) (Fin m) T

/-! ## 1. The float grid as a wmap into ℚ -/

/-- `k+1` equally spaced rationals `lo, lo+s, …, lo+k*s`. -/
structure Grid where
  lo : ℚ
  s : ℚ
  k : ℕ
  hs : 0 < s

namespace Grid

variable (g : Grid)

def embed (i : Fin (g.k + 1)) : ℚ := g.lo + g.s * ((i : ℕ) : ℚ)

def hi : ℚ := g.lo + g.s * g.k

/-- Nearest grid index, clamped to `[0, k]`. -/
def round (x : ℚ) : Fin (g.k + 1) :=
  ⟨min g.k (⌊(x - g.lo) / g.s + 1 / 2⌋).toNat, Nat.lt_succ_of_le (min_le_left _ _)⟩

/-- Half the spacing: the worst-case rounding error. -/
def half : ℚ := g.s / 2

theorem half_pos : 0 < g.half := by unfold half; linarith [g.hs]

theorem round_eq_of_near {x : ℚ} {i : Fin (g.k + 1)} (h : |x - g.embed i| < g.half) :
    g.round x = i := by
  have hs := g.hs
  unfold half embed at *
  have hu : (x - g.lo) / g.s = (i : ℕ) + (x - (g.lo + g.s * (i : ℕ))) / g.s := by
    field_simp; ring
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  have hq1 : -(1 / 2 : ℚ) < (x - (g.lo + g.s * (i : ℕ))) / g.s := by
    rw [lt_div_iff₀ hs]; linarith
  have hq2 : (x - (g.lo + g.s * (i : ℕ))) / g.s < 1 / 2 := by
    rw [div_lt_iff₀ hs]; linarith
  have hfl : ⌊(x - g.lo) / g.s + 1 / 2⌋ = ((i : ℕ) : ℤ) := by
    rw [Int.floor_eq_iff, hu]; push_cast; constructor <;> linarith
  apply Fin.ext
  simp only [round, hfl, Int.toNat_natCast]
  exact min_eq_right (Nat.le_of_lt_succ i.isLt)

theorem round_embed (i : Fin (g.k + 1)) : g.round (g.embed i) = i :=
  g.round_eq_of_near (by simpa using g.half_pos)

theorem round_err {x : ℚ} (h1 : g.lo ≤ x) (h2 : x ≤ g.hi) :
    |g.embed (g.round x) - x| ≤ g.half := by
  have hs := g.hs
  unfold hi at h2
  set u := (x - g.lo) / g.s with hu_def
  have hxu : x = g.lo + g.s * u := by rw [hu_def]; field_simp; ring
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hs.le
  have huk : u ≤ g.k := by rw [hu_def, div_le_iff₀ hs]; linarith
  set j := ⌊u + 1 / 2⌋ with hj_def
  have hj0 : 0 ≤ j := Int.floor_nonneg.mpr (by linarith)
  have hjle : (j : ℚ) ≤ u + 1 / 2 := Int.floor_le _
  have hjgt : u + 1 / 2 < j + 1 := Int.lt_floor_add_one _
  have hjk : j ≤ g.k := by
    have : (j : ℚ) < (g.k : ℚ) + 1 := by linarith
    exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
  have hcast : ((j.toNat : ℕ) : ℚ) = (j : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hj0
  have hmin : min g.k j.toNat = j.toNat := min_eq_right (by omega)
  have he : g.embed (g.round x) = g.lo + g.s * (j : ℚ) := by
    simp only [embed, round, ← hj_def, ← hu_def, hmin, hcast]
  rw [he, hxu, abs_le]
  unfold half
  constructor <;> nlinarith

/-- Symmetric grid on `[-R, R]` with `k` steps; its rounding error is `R / k`. -/
def symGrid (R : ℚ) (k : ℕ) (hR : 0 < R) (hk : 0 < k) : Grid :=
  ⟨-R, 2 * R / k, k, by positivity⟩

theorem symGrid_half (R : ℚ) (k : ℕ) (hR : 0 < R) (hk : 0 < k) :
    (symGrid R k hR hk).half = R / k := by
  simp only [symGrid, half]; ring

/-- More grid points, smaller rounding error. -/
theorem symGrid_half_antitone (R : ℚ) (hR : 0 < R) {k₁ k₂ : ℕ} (hk₁ : 0 < k₁) (h : k₁ ≤ k₂) :
    (symGrid R k₂ hR (lt_of_lt_of_le hk₁ h)).half ≤ (symGrid R k₁ hR hk₁).half := by
  rw [symGrid_half, symGrid_half]
  exact div_le_div_of_nonneg_left hR.le (by exact_mod_cast hk₁) (by exact_mod_cast h)

/-- With `b` bits the rounding error `R / 2^b` gets below any tolerance. -/
theorem symGrid_half_bits_small (R : ℚ) (hR : 0 < R) {ε : ℚ} (hε : 0 < ε) :
    ∃ B, ∀ b ≥ B, (symGrid R (2 ^ b) hR (by positivity)).half < ε := by
  obtain ⟨B, hB⟩ := exists_nat_gt (R / ε)
  refine ⟨B, fun b hb => ?_⟩
  rw [symGrid_half, div_lt_iff₀ (by positivity)]
  have h1 : (B : ℚ) ≤ b := by exact_mod_cast hb
  have h2 : (b : ℚ) < ((2 ^ b : ℕ) : ℚ) := by exact_mod_cast Nat.lt_two_pow_self
  rw [div_lt_iff₀ hε] at hB
  nlinarith

/-! ### Transport of operations -/

def gridWmap : wmap (Fin (g.k + 1)) ℚ := mkwmap g.embed g.round g.round_embed

/-- Exact direction: a grid operation moved onto `ℚ` by `hmor2_exists`. Rounding
is an exact homomorphism from it back to the grid operation. -/
def transportOp (op : Fin (g.k + 1) → Fin (g.k + 1) → Fin (g.k + 1)) : ℚ → ℚ → ℚ :=
  (hmor2_exists g.gridWmap op).1

theorem transportOp_hmor2 (op : Fin (g.k + 1) → Fin (g.k + 1) → Fin (g.k + 1)) :
    hmor2 op (g.transportOp op) g.round :=
  (hmor2_exists g.gridWmap op).2.1

/-- Rounded direction (what low-precision kernels do): a `ℚ` operation computed on the grid. -/
def roundOp (op : ℚ → ℚ → ℚ) (a b : Fin (g.k + 1)) : Fin (g.k + 1) :=
  g.round (op (g.embed a) (g.embed b))

/-- `embed` is only an approximate homomorphism for rounded operations. -/
theorem approx_hmor2 (op : ℚ → ℚ → ℚ) (a b : Fin (g.k + 1))
    (h1 : g.lo ≤ op (g.embed a) (g.embed b)) (h2 : op (g.embed a) (g.embed b) ≤ g.hi) :
    |g.embed (g.roundOp op a b) - op (g.embed a) (g.embed b)| ≤ g.half :=
  g.round_err h1 h2

def embedM {n m} (W : Matr n m (Fin (g.k + 1))) : Matr n m ℚ := W.map g.embed

def roundM {n m} (W : Matr n m ℚ) : Matr n m (Fin (g.k + 1)) := W.map g.round

end Grid

/-! ## 2. A derivative defined by operations over ℚ -/

section Smooth

variable {n m : ℕ}

def minner (a b : Matr n m ℚ) : ℚ := ∑ p : Fin n × Fin m, a p.1 p.2 * b p.1 p.2

def msq (a : Matr n m ℚ) : ℚ := minner a a

/-- `grad` is a derivative of `ℓ` with curvature bound `L`: first-order Taylor with a
quadratic remainder. No limits, so it makes sense on bounded fractions. -/
def SmoothWith (ℓ : Matr n m ℚ → ℚ) (grad : Matr n m ℚ → Matr n m ℚ) (L : ℚ) : Prop :=
  ∀ w d, |ℓ (w + d) - ℓ w - minner (grad w) d| ≤ L / 2 * msq d

theorem sq_nonneg' (a : Matr n m ℚ) : 0 ≤ msq a :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem sq_le_of_entry_le {e : Matr n m ℚ} {ε : ℚ} (h : ∀ i j, |e i j| ≤ ε) :
    msq e ≤ (n * m : ℚ) * ε ^ 2 := by
  have : ∀ p ∈ (Finset.univ : Finset (Fin n × Fin m)), e p.1 p.2 * e p.1 p.2 ≤ ε ^ 2 := by
    intro p _
    obtain ⟨h1, h2⟩ := abs_le.mp (h p.1 p.2)
    nlinarith
  calc msq e ≤ ∑ _p : Fin n × Fin m, ε ^ 2 := Finset.sum_le_sum this
    _ = (n * m : ℚ) * ε ^ 2 := by simp [Finset.card_univ, Fintype.card_prod]

end Smooth

/-! ## 3. Training as a `Seqv` -/

section Training

variable {n m : ℕ} (g : Grid) (η : ℚ) (gradQ : Matr n m ℚ → Matr n m ℚ)

/-- One step of gradient descent with weights stored on the grid. `gradQ` is the gradient
actually computed (for instance itself rounded to another grid). -/
def step (W : Matr n m (Fin (g.k + 1))) : Matr n m (Fin (g.k + 1)) :=
  g.roundM (g.embedM W - η • gradQ (g.embedM W))

def train (W₀ : Matr n m (Fin (g.k + 1))) : Seqv (Matr n m (Fin (g.k + 1))) :=
  fun t => iterf t (step g η gradQ) W₀

def lossSeq (ℓ : Matr n m ℚ → ℚ) (W₀ : Matr n m (Fin (g.k + 1))) : Seqv ℚ :=
  fun t => ℓ (g.embedM (train g η gradQ W₀ t))

def gradSeq (grad : Matr n m ℚ → Matr n m ℚ) (W₀ : Matr n m (Fin (g.k + 1))) :
    Seqv (Matr n m ℚ) :=
  fun t => grad (g.embedM (train g η gradQ W₀ t))

theorem train_succ (W₀ : Matr n m (Fin (g.k + 1))) (t : ℕ) :
    train g η gradQ W₀ (t + 1) = step g η gradQ (train g η gradQ W₀ t) :=
  iterf_step_eqn

/-- The update before rounding stays inside the grid's range. -/
def InRange (W : Matr n m (Fin (g.k + 1))) : Prop :=
  ∀ i j, g.lo ≤ (g.embedM W - η • gradQ (g.embedM W)) i j ∧
    (g.embedM W - η • gradQ (g.embedM W)) i j ≤ g.hi

/-- Per-entry algebra behind the descent lemma. -/
private theorem entry_bound {η a e : ℚ} (hη : 0 < η) :
    a * e ≤ η / 4 * (a * a) + e * e / η := by
  rw [← sub_nonneg]
  have : η / 4 * (a * a) + e * e / η - a * e = (η * a - 2 * e) ^ 2 / (4 * η) := by
    field_simp; ring
  rw [this]; positivity

variable {g η gradQ}

/-- **Descent lemma on a grid.** One step lowers the loss by `η/4 · ‖∇ℓ‖²`, up to an error
term that is quadratic in the rounding error `ε = s/2 + η·εg`. -/
theorem descent_step {ℓ : Matr n m ℚ → ℚ} {grad : Matr n m ℚ → Matr n m ℚ} {L εg : ℚ}
    (hsm : SmoothWith ℓ grad L) (hL : 0 ≤ L) (hη : 0 < η) (hηL : L * η ≤ 1 / 2)
    (hgQ : ∀ w i j, |gradQ w i j - grad w i j| ≤ εg)
    (W : Matr n m (Fin (g.k + 1))) (hr : InRange g η gradQ W) :
    ℓ (g.embedM (step g η gradQ W)) ≤
      ℓ (g.embedM W) - η / 4 * msq (grad (g.embedM W))
        + (1 / η + L) * ((n * m : ℚ) * (g.half + η * εg) ^ 2) := by
  set w := g.embedM W
  set gr := grad w
  set d := g.embedM (step g η gradQ W) - w with hd
  set e := d + η • gr with he
  have hwd : w + d = g.embedM (step g η gradQ W) := by rw [hd]; abel
  -- entrywise: the step is `-η·grad` plus a small error `e`
  have he_entry : ∀ i j, |e i j| ≤ g.half + η * εg := by
    intro i j
    have hrnd := g.round_err (hr i j).1 (hr i j).2
    have hq := hgQ w i j
    have : e i j = (g.embed (g.round ((w - η • gradQ w) i j)) - (w - η • gradQ w) i j)
        + η * (gr i j - gradQ w i j) := by
      simp only [he, hd, step, Grid.embedM, Grid.roundM, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, gr, w]
      ring
    rw [this]
    calc _ ≤ |g.embed (g.round ((w - η • gradQ w) i j)) - (w - η • gradQ w) i j|
            + |η * (gr i j - gradQ w i j)| := abs_add_le _ _
      _ ≤ g.half + η * εg := by
        rw [abs_mul, abs_of_pos hη]
        gcongr
        rw [abs_sub_comm]; exact hq
  have hsqe := sq_le_of_entry_le he_entry
  -- minner and square bounds, summed entrywise
  have hinner : minner gr d ≤ -(3 * η / 4) * msq gr + msq e / η := by
    have hde : ∀ p : Fin n × Fin m, d p.1 p.2 = -(η * gr p.1 p.2) + e p.1 p.2 := by
      intro p; simp only [he, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    unfold minner msq minner
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [hde p]
    have := entry_bound (a := gr p.1 p.2) (e := e p.1 p.2) hη
    rw [show gr p.1 p.2 * (-(η * gr p.1 p.2) + e p.1 p.2)
        = -η * (gr p.1 p.2 * gr p.1 p.2) + gr p.1 p.2 * e p.1 p.2 by ring]
    linarith
  have hsqd : msq d ≤ 2 * η ^ 2 * msq gr + 2 * msq e := by
    have hde : ∀ p : Fin n × Fin m, d p.1 p.2 = -(η * gr p.1 p.2) + e p.1 p.2 := by
      intro p; simp only [he, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    unfold msq minner
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [hde p]
    nlinarith [sq_nonneg (η * gr p.1 p.2 + e p.1 p.2)]
  have htay := (abs_le.mp (hsm w d)).2
  rw [hwd] at htay
  have hsqgr := sq_nonneg' gr
  have hsqe0 := sq_nonneg' e
  have hLsqd : L / 2 * msq d ≤ L * η ^ 2 * msq gr + L * msq e := by nlinarith
  have hLη : L * η ^ 2 * msq gr ≤ η / 2 * msq gr := by
    have := mul_nonneg (mul_nonneg (sub_nonneg.mpr hηL) hη.le) hsqgr
    nlinarith [this]
  have hdiv : msq e / η ≤ ((n * m : ℚ) * (g.half + η * εg) ^ 2) / η :=
    div_le_div_of_nonneg_right hsqe hη.le
  have hLe : L * msq e ≤ L * ((n * m : ℚ) * (g.half + η * εg) ^ 2) :=
    mul_le_mul_of_nonneg_left hsqe hL
  have hsplit : (1 / η + L) * ((n * m : ℚ) * (g.half + η * εg) ^ 2)
      = ((n * m : ℚ) * (g.half + η * εg) ^ 2) / η + L * ((n * m : ℚ) * (g.half + η * εg) ^ 2) := by
    ring
  rw [hsplit]
  linarith

variable {ℓ : Matr n m ℚ → ℚ} {grad : Matr n m ℚ → Matr n m ℚ} {L εg : ℚ}

/-- The error floor of one step. -/
def floorC (g : Grid) (η L εg : ℚ) (n m : ℕ) : ℚ :=
  (1 / η + L) * ((n * m : ℚ) * (g.half + η * εg) ^ 2)

/-- Along the training `Seqv`: loss strictly decreases whenever the gradient dominates the floor. -/
theorem loss_decreases (hsm : SmoothWith ℓ grad L) (hL : 0 ≤ L) (hη : 0 < η)
    (hηL : L * η ≤ 1 / 2) (hgQ : ∀ w i j, |gradQ w i j - grad w i j| ≤ εg)
    (W₀ : Matr n m (Fin (g.k + 1))) (t : ℕ) (hr : InRange g η gradQ (train g η gradQ W₀ t))
    (hbig : floorC g η L εg n m < η / 4 * msq (gradSeq g η gradQ grad W₀ t)) :
    lossSeq g η gradQ ℓ W₀ (t + 1) < lossSeq g η gradQ ℓ W₀ t := by
  have := descent_step hsm hL hη hηL hgQ _ hr
  simp only [lossSeq, gradSeq, floorC] at *
  rw [train_succ]
  linarith

/-- Summed over `T` steps: the total squared gradient is bounded by the loss drop plus
`T` times the floor. Divided by `T`, the average squared gradient is at most
`4(ℓ₀ - ℓmin)/(ηT) + 4·floorC/η`. -/
theorem loss_floor (hsm : SmoothWith ℓ grad L) (hL : 0 ≤ L) (hη : 0 < η)
    (hηL : L * η ≤ 1 / 2) (hgQ : ∀ w i j, |gradQ w i j - grad w i j| ≤ εg)
    (W₀ : Matr n m (Fin (g.k + 1))) (hr : ∀ t, InRange g η gradQ (train g η gradQ W₀ t))
    {ℓmin : ℚ} (hmin : ∀ w, ℓmin ≤ ℓ w) (T : ℕ) :
    η / 4 * ∑ t ∈ Finset.range T, msq (gradSeq g η gradQ grad W₀ t)
      ≤ lossSeq g η gradQ ℓ W₀ 0 - ℓmin + T * floorC g η L εg n m := by
  suffices h : ∀ T, η / 4 * ∑ t ∈ Finset.range T, msq (gradSeq g η gradQ grad W₀ t)
      ≤ lossSeq g η gradQ ℓ W₀ 0 - lossSeq g η gradQ ℓ W₀ T + T * floorC g η L εg n m by
    have := hmin (g.embedM (train g η gradQ W₀ T))
    have := h T
    simp only [lossSeq] at *
    linarith
  intro T
  induction T with
  | zero => simp
  | succ T ih =>
    have hstep := descent_step hsm hL hη hηL hgQ _ (hr T)
    rw [Finset.sum_range_succ, mul_add]
    simp only [lossSeq, gradSeq, floorC] at *
    rw [train_succ]
    push_cast
    linarith

/-- **Stall.** If every update is smaller than half a grid step, rounding undoes it. -/
theorem stall (W : Matr n m (Fin (g.k + 1)))
    (hsmall : ∀ i j, |η * gradQ (g.embedM W) i j| < g.half) :
    step g η gradQ W = W := by
  funext i j
  apply g.round_eq_of_near
  simp only [Grid.embedM, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [show g.embed (W i j) - η * gradQ (W.map g.embed) i j - g.embed (W i j)
      = -(η * gradQ (W.map g.embed) i j) by ring, abs_neg]
  exact hsmall i j

theorem stall_forever (W₀ : Matr n m (Fin (g.k + 1)))
    (hsmall : ∀ i j, |η * gradQ (g.embedM W₀) i j| < g.half) (t : ℕ) :
    train g η gradQ W₀ t = W₀ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [train_succ, ih, stall W₀ hsmall]

end Training

/-! ## 4. A concrete 1×1 example -/

namespace Example

/-- Grid `{-1, -1/2, 0, 1/2, 1}`. -/
def g5 : Grid := ⟨-1, 1 / 2, 4, by norm_num⟩

/-- Loss `(w - c)²`, minimised at `c`. -/
def ℓq (c : ℚ) (w : Matr 1 1 ℚ) : ℚ := (w 0 0 - c) ^ 2

def gradq (c : ℚ) (w : Matr 1 1 ℚ) : Matr 1 1 ℚ := fun _ _ => 2 * (w 0 0 - c)

theorem smooth_q (c : ℚ) : SmoothWith (ℓq c) (gradq c) 2 := by
  intro w d
  have hs : ∀ f : Fin 1 × Fin 1 → ℚ, ∑ p, f p = f (0, 0) := fun f => by
    simp [Fintype.sum_prod_type]
  simp only [ℓq, gradq, msq, minner, hs, Matrix.add_apply]
  rw [show (w 0 0 + d 0 0 - c) ^ 2 - (w 0 0 - c) ^ 2 - 2 * (w 0 0 - c) * d 0 0
      = d 0 0 * d 0 0 by ring, abs_of_nonneg (mul_self_nonneg _)]
  linarith

/-- Start at `0` with target `1/10` and `η = 1/4`: the update `1/20` is below half a grid step
(`1/4`), so training stays at `0` forever and the loss never drops below `1/100`. -/
def W0 : Matr 1 1 (Fin (g5.k + 1)) := fun _ _ => (2 : Fin 5)

theorem example_stalls (t : ℕ) : train g5 (1 / 4) (gradq (1 / 10)) W0 t = W0 := by
  apply stall_forever
  intro i j
  simp [Grid.embedM, gradq, W0, g5, Grid.embed, Grid.half]
  norm_num


-- With `k = 4` and target `1/2`, which lies on the grid, the loss falls to 0.
#eval (lossSeq g5 (1 / 4) (gradq (1 / 2)) (ℓq (1 / 2)) W0).truncate 6

-- With target `1/10`, off the grid, training stalls at loss `1/100`.
#eval (lossSeq g5 (1 / 4) (gradq (1 / 10)) (ℓq (1 / 10)) W0).truncate 6

end Example
