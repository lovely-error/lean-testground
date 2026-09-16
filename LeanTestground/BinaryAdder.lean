import LeanTestground.Quantization

/-!
# A grid-weight network that learns u32 addition

Scheme:

1. **Specification.** `u32` addition is bit-serial: a full adder run over the 32 bits of
   both inputs, carry fed forward (`runAdder`, a `Seqv` of sum bits). `serial_correct`
   proves any cell equal to `fullAdder` adds every pair of `u32` exactly (mod 2³²).
2. **Network.** A 3→4→2 cell with rational sigmoid `σ z = 1/2 + z / (2(1+|z|))`. Its 26
   parameters are one `Matr 1 26`, so the `Grid` training of `Quantization.lean` applies
   unchanged. Weights stay on the grid, so rational sizes stay bounded.
3. **Data.** Random `u32` pairs. Each pair yields 32 (x, y, carry-in) → (sum, carry-out)
   examples using the true carry (teacher forcing), so training is not recurrent.
   Only 8 patterns exist; the data enters as their counts.
4. **Training.** `train` from `Quantization.lean` with the exact backprop gradient.
5. **Certificate.** At inference the cell's outputs are thresholded at `1/2`, so the carry
   fed back is always a bit and the cell only ever sees the 8 patterns. Checking those 8
   (`certificate`) proves the trained network adds **all** 2⁶⁴ input pairs (`learned_adds`).
-/

namespace BinAdd

/-! ## 1. Specification -/

def fullAdder (x y c : Bool) : Bool × Bool :=
  (xor (xor x y) c, (x && y) || (c && xor x y))

abbrev Cell := Bool → Bool → Bool → Bool × Bool

/-- Bits of a number, least significant first. -/
def bits (a : ℕ) : Seqv Bool := fun i => a.testBit i

/-- Carry into position `i`. -/
def carry (cell : Cell) (xs ys : Seqv Bool) : ℕ → Bool
  | 0 => false
  | i + 1 => (cell (xs i) (ys i) (carry cell xs ys i)).2

def sumBits (cell : Cell) (xs ys : Seqv Bool) : Seqv Bool :=
  fun i => (cell (xs i) (ys i) (carry cell xs ys i)).1

/-- The number whose low `n` bits are the first `n` entries of `s`. -/
def fromBits (s : Seqv Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => fromBits s n + (s n).toNat * 2 ^ n

def runAdder (cell : Cell) (a b : UInt32) : UInt32 :=
  UInt32.ofNat (fromBits (sumBits cell (bits a.toNat) (bits b.toNat)) 32)

theorem fullAdder_value (x y c : Bool) :
    (fullAdder x y c).1.toNat + 2 * (fullAdder x y c).2.toNat = x.toNat + y.toNat + c.toNat := by
  cases x <;> cases y <;> cases c <;> rfl

theorem fromBits_lt (s : Seqv Bool) (n : ℕ) : fromBits s n < 2 ^ n := by
  induction n with
  | zero => simp [fromBits]
  | succ n ih =>
    have : (s n).toNat ≤ 1 := Bool.toNat_le _
    simp only [fromBits, pow_succ]
    nlinarith

theorem mod_two_pow_succ' (x i : ℕ) : x % 2 ^ (i + 1) = x % 2 ^ i + (x.testBit i).toNat * 2 ^ i := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h, mul_comm]

/-- Loop invariant of the serial adder. -/
theorem adder_invariant (a b n : ℕ) :
    fromBits (sumBits fullAdder (bits a) (bits b)) n
      + (carry fullAdder (bits a) (bits b) n).toNat * 2 ^ n = a % 2 ^ n + b % 2 ^ n := by
  induction n with
  | zero => simp [fromBits, carry, Nat.mod_one]
  | succ n ih =>
    have hv := fullAdder_value (bits a n) (bits b n) (carry fullAdder (bits a) (bits b) n)
    simp only [fromBits, carry, sumBits] at *
    rw [mod_two_pow_succ' a n, mod_two_pow_succ' b n]
    simp only [bits] at *
    rw [pow_succ]
    have h2 := congrArg (fun t => t * 2 ^ n) hv
    simp only at h2
    nlinarith [h2]

theorem serial_correct (cell : Cell) (h : ∀ x y c, cell x y c = fullAdder x y c)
    (a b : UInt32) : runAdder cell a b = a + b := by
  have hc : cell = fullAdder := funext fun x => funext fun y => funext fun c => h x y c
  subst hc
  unfold runAdder
  have inv := adder_invariant a.toNat b.toNat 32
  have hlt := fromBits_lt (sumBits fullAdder (bits a.toNat) (bits b.toNat)) 32
  set F := fromBits (sumBits fullAdder (bits a.toNat) (bits b.toNat)) 32
  have hF : F = (a.toNat + b.toNat) % 2 ^ 32 := by
    rw [Nat.add_mod, ← inv, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', UInt32.toNat_add, hF, Nat.mod_mod]

/-! ## 2. The network cell -/

/-- Parameters: `W1 : 4 × 4` (inputs x, y, c, 1) then `W2 : 2 × 5` (hidden, 1). -/
abbrev P := 26

def w1 (θ : Matr 1 P ℚ) (h i : Fin 4) : ℚ := θ 0 ⟨h * 4 + i, by unfold P; omega⟩
def w2 (θ : Matr 1 P ℚ) (o : Fin 2) (j : Fin 5) : ℚ := θ 0 ⟨16 + o * 5 + j, by unfold P; omega⟩

def σ (z : ℚ) : ℚ := 1 / 2 + z / (2 * (1 + |z|))
def σ' (z : ℚ) : ℚ := 1 / (2 * (1 + |z|) ^ 2)

def input (x y c : Bool) : Fin 4 → ℚ := ![x.toNat, y.toNat, c.toNat, 1]

structure Fwd where
  z1 : Fin 4 → ℚ
  u : Fin 5 → ℚ     -- hidden activations, then the constant 1
  z2 : Fin 2 → ℚ
  out : Fin 2 → ℚ

/-- Forward pass; `r` is applied at every node (`id` for exact ℚ, `fx` for fixed point). -/
def forwardWith (r : ℚ → ℚ) (θ : Matr 1 P ℚ) (v : Fin 4 → ℚ) : Fwd :=
  let z1 : Fin 4 → ℚ := fun h =>
    r ((List.finRange 4).foldl (fun s i => s + w1 θ h i * v i) 0)
  let u : Fin 5 → ℚ := Fin.lastCases 1 (fun h => r (σ (z1 h)))
  let z2 : Fin 2 → ℚ := fun o =>
    r ((List.finRange 5).foldl (fun s j => s + w2 θ o j * u j) 0)
  ⟨z1, u, z2, fun o => r (σ (z2 o))⟩

/-- Exact forward pass over ℚ; this is what the certificate checks. -/
def forward : Matr 1 P ℚ → (Fin 4 → ℚ) → Fwd := forwardWith id

/-- Fixed-point rounding to multiples of `2⁻²⁰`, like a low-precision kernel. -/
def fx (q : ℚ) : ℚ := (⌊q * 2 ^ 20 + 1 / 2⌋ : ℚ) / 2 ^ 20

def boolQ (b : Bool) : ℚ := b.toNat

/-- The 8 input patterns. -/
def pattern (p : Fin 8) : Bool × Bool × Bool :=
  (p.val.testBit 0, p.val.testBit 1, p.val.testBit 2)

/-- Weighted squared-error loss; `cnt p` is how often pattern `p` occurs in the data. -/
def loss (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) : ℚ :=
  ∑ p, let (x, y, c) := pattern p
       let f := forward θ (input x y c)
       let t := fullAdder x y c
       (cnt p : ℚ) * ((f.out 0 - boolQ t.1) ^ 2 + (f.out 1 - boolQ t.2) ^ 2) / 2

/-- Backpropagated gradient, with `r` applied at every node, computed into an array once.
The output delta is `out - target` (no `σ'` factor), the analogue of sigmoid with
cross-entropy: it is the exact gradient of the loss `Σ ∫ (σ z - t) dz`, which does not
flatten out when an output saturates on the wrong side. Squared error does, and training
then stalls on the grid (see `stall`). With `r = fx` this is the `gradQ` of
`Quantization.lean`: close to the exact gradient, with bounded rationals. -/
def gradArr (r : ℚ → ℚ) (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) : Array ℚ := Id.run do
  let mut g : Array ℚ := Array.replicate P 0
  for p in List.finRange 8 do
    let (x, y, c) := pattern p
    let v := input x y c
    let f := forwardWith r θ v
    let t := fullAdder x y c
    let n : ℚ := cnt p
    let d2 : Fin 2 → ℚ := ![r (n * (f.out 0 - boolQ t.1)), r (n * (f.out 1 - boolQ t.2))]
    for o in List.finRange 2 do
      for j in List.finRange 5 do
        let k := 16 + o.val * 5 + j.val
        g := g.modify k (· + r (d2 o * f.u j))
    for h in List.finRange 4 do
      let back := d2 0 * w2 θ 0 h.castSucc + d2 1 * w2 θ 1 h.castSucc
      let d1 := r (back * σ' (f.z1 h))
      for i in List.finRange 4 do
        let k := h.val * 4 + i.val
        g := g.modify k (· + d1 * v i)
  return g

def grad (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) : Matr 1 P ℚ :=
  let a := gradArr fx cnt θ
  fun _ j => a.getD j 0

/-! ## 3. Data from u32 pairs -/

def lcg (s : UInt32) : UInt32 := s * 1664525 + 1013904223

def randomPairs (n : ℕ) (seed : UInt32) : List (UInt32 × UInt32) :=
  (List.range n).foldl (fun (acc, s) _ => let s1 := lcg s; let s2 := lcg s1
    ((s1, s2) :: acc, s2)) ([], seed) |>.1

def patternIndex (x y c : Bool) : ℕ := x.toNat + 2 * y.toNat + 4 * c.toNat

/-- Pattern counts over all 32 bit positions of the pairs, using the true carry. -/
def counts (pairs : List (UInt32 × UInt32)) : Fin 8 → ℕ := Id.run do
  let mut cs : Array ℕ := Array.replicate 8 0
  for (a, b) in pairs do
    let mut c := false
    for i in List.range 32 do
      let x := a.toNat.testBit i
      let y := b.toNat.testBit i
      cs := cs.modify (patternIndex x y c) (· + 1)
      c := (fullAdder x y c).2
  return fun p => cs.getD p 0

/-! ## 4. Training on a grid -/

theorem getD_ofFn {α} {n} (f : Fin n → α) (j : Fin n) (d : α) :
    (Array.ofFn f).getD j d = f j := by
  simp [Array.getD, j.isLt]

/-- Weights as a plain array of grid indices (entries clamped into the grid). -/
def ofArr (g : Grid) (a : Array ℕ) : Matr 1 P (Fin (g.k + 1)) :=
  fun _ j => ⟨min g.k (a.getD j 0), Nat.lt_succ_of_le (min_le_left _ _)⟩

/-- One step, given the gradient `G` already computed. -/
def stepCore (g : Grid) (η : ℚ) (a : Array ℕ) (G : Array ℚ) : Array ℕ :=
  Array.ofFn fun j : Fin P => (g.round (g.embed (ofArr g a 0 j) - η * G.getD j 0)).val

/-- `step` on arrays. The gradient is an argument of `stepCore`, so it is evaluated once per
step; matrices as closures would recompute earlier steps again and again. -/
def stepArr (g : Grid) (η : ℚ) (cnt : Fin 8 → ℕ) (a : Array ℕ) : Array ℕ :=
  stepCore g η a (gradArr fx cnt (g.embedM (ofArr g a)))

theorem ofArr_stepArr (g : Grid) (η : ℚ) (cnt : Fin 8 → ℕ) (a : Array ℕ) :
    ofArr g (stepArr g η cnt a) = step g η (grad cnt) (ofArr g a) := by
  funext i j
  apply Fin.ext
  show min g.k ((stepArr g η cnt a).getD j 0) = _
  rw [stepArr, stepCore, getD_ofFn]
  exact min_eq_right (Nat.le_of_lt_succ (Fin.isLt _))

/-- Iterating the array step is exactly the `Seqv` `train` of `Quantization.lean`. -/
theorem iterf_stepArr (g : Grid) (η : ℚ) (cnt : Fin 8 → ℕ) (a : Array ℕ) (t : ℕ) :
    ofArr g (iterf t (stepArr g η cnt) a) = train g η (grad cnt) (ofArr g a) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [train_succ, ← ih]; exact ofArr_stepArr g η cnt _

/-- A fixed point of the step is final: training never moves again. -/
theorem stall_of_fixed {g : Grid} {η : ℚ} {cnt : Fin 8 → ℕ} {a : Array ℕ}
    (h : stepArr g η cnt a = a) (t : ℕ) : train g η (grad cnt) (ofArr g a) t = ofArr g a := by
  have hit : ∀ t, iterf t (stepArr g η cnt) a = a := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [iterf_step_eqn, ih, h]
  rw [← iterf_stepArr, hit]

/-- Random start near 0: each weight is the middle grid index plus up to `±spread` steps. -/
def initArr (g : Grid) (spread : ℕ) (seed : UInt32) : Array ℕ := Id.run do
  let mut s := seed
  let mut a : Array ℕ := #[]
  for _ in List.range P do
    s := lcg s
    let off := (s >>> 8).toNat % (2 * spread + 1)
    a := a.push (min g.k (g.k / 2 + off - spread))
  return a

/-! ## 5. Certificate: 8 checks ⇒ correct on all u32 -/

def cellOf (θ : Matr 1 P ℚ) : Cell := fun x y c =>
  let f := forward θ (input x y c)
  (decide (1 / 2 < f.out 0), decide (1 / 2 < f.out 1))

def certificate (θ : Matr 1 P ℚ) : Bool :=
  (List.finRange 8).all fun p =>
    let (x, y, c) := pattern p
    cellOf θ x y c == fullAdder x y c

theorem cert_sound {θ : Matr 1 P ℚ} (h : certificate θ = true) (x y c : Bool) :
    cellOf θ x y c = fullAdder x y c := by
  have hp : ∀ p : Fin 8, cellOf θ (pattern p).1 (pattern p).2.1 (pattern p).2.2
      = fullAdder (pattern p).1 (pattern p).2.1 (pattern p).2.2 := by
    intro p
    have := List.all_eq_true.mp h p (List.mem_finRange p)
    simpa using this
  have key : ∃ p : Fin 8, pattern p = (x, y, c) := by
    refine ⟨⟨patternIndex x y c, ?_⟩, ?_⟩
    · cases x <;> cases y <;> cases c <;> decide
    · cases x <;> cases y <;> cases c <;> decide
  obtain ⟨p, hp'⟩ := key
  have := hp p
  rw [hp'] at this
  exact this

/-- **Main theorem.** Weights passing the 8-pattern certificate add every pair of u32. -/
theorem learned_adds {θ : Matr 1 P ℚ} (h : certificate θ = true) (a b : UInt32) :
    runAdder (cellOf θ) a b = a + b :=
  serial_correct _ (cert_sound h) a b

/-! ## 6. Training runs and the trained network -/

/-- Training data: pattern counts of 64 random u32 pairs (2048 bit positions). -/
def cnt : Fin 8 → ℕ := counts (randomPairs 64 12345)

/-- Fine grid: [-32, 32] in steps of 1/64. -/
def gFine : Grid := ⟨-32, 1 / 64, 4096, by norm_num⟩
def a0 : Array ℕ := initArr gFine 32 7

def qf (q : ℚ) : Float := Float.ofInt ⌊q * 1000000⌋ / 1000000

inductive Outcome where
  | certified (t : ℕ)
  | stalled (t : ℕ)
  | budget
  deriving Repr

/-- Train for up to `T` steps, logging squared error every `every` steps. Stop when the
certificate passes, or at a fixed point (`stall_of_fixed`: nothing would change afterwards). -/
def trace (g : Grid) (η : ℚ) (a : Array ℕ) (T every : ℕ) :
    List (ℕ × Float) × Array ℕ × Outcome := Id.run do
  let mut a := a
  let mut out := []
  for t in List.range (T + 1) do
    let θ := g.embedM (ofArr g a)
    if t % every == 0 then
      out := (t, qf (loss cnt θ / 2048)) :: out
      if certificate θ then
        return (out.reverse, a, .certified t)
    if t < T then
      let a' := stepArr g η cnt a
      if a' == a then
        return (out.reverse, a, .stalled t)
      a := a'
  return (out.reverse, a, .budget)

def report (name : String) (g : Grid) (η : ℚ) (a : Array ℕ) (T every : ℕ) : IO Unit := do
  let (tr, aT, res) ← pure (trace g η a T every)
  IO.println s!"{name}: sq-error {tr}"
  IO.println s!"  outcome {repr res}"
  IO.println s!"  weight indices {aT}"
  IO.println s!"  certificate {certificate (g.embedM (ofArr g aT))}"

/-- Weights (grid indices of `gFine`) reached from `a0` after 825 steps with `η = 1/512`.
`BinaryAdderRun.lean` reproduces them. -/
def learned : Array ℕ :=
  #[2773, 2756, 2801, 1065, 1672, 1685, 1654, 2563, 2402, 2431, 2365, 1880, 1779,
    1783, 1773, 2615, 827, 2164, 3888, 1698, 1507, 4096, 63, 2818, 236, 2031]

theorem learned_certified : certificate (gFine.embedM (ofArr gFine learned)) = true := by
  decide +kernel

/-- **The trained network adds u32.** For all 2⁶⁴ input pairs. -/
theorem trained_net_adds (a b : UInt32) :
    runAdder (cellOf (gFine.embedM (ofArr gFine learned))) a b = a + b :=
  learned_adds learned_certified a b

end BinAdd
