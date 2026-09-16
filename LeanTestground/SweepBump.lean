import LeanTestground.Sweep

/-!
# The sweep again, with activation `σ(x) = 1/2 + x/(1+x²)`

Everything but the activation matches `Sweep.lean`: the same grids on `[-32, 32]`, the same
10 paired seeds and real starting weights, `η = 1/512`, the fixed-point gradient with output
delta `out - target`, and the same stopping rules.

The activation has range `[0, 1]`, peaks at `σ(1) = 1`, bottoms out at `σ(-1) = 0`, and tends
to `1/2` as `|x| → ∞`, so large pre-activations do not saturate. It still satisfies
`σ x > 1/2 ↔ x > 0`, so the certificate threshold means the same, and `certB_sound` /
`learnedB_adds` give correctness on all u32 exactly as before.

Not imported by the library. Build `LeanTestground.Sweep` first (without `SWEEP_*` variables
set), then run a group with `BUMP_GROUP=<n> lake env lean LeanTestground/SweepBump.lean`.
-/

open BinAdd Sweep

namespace SweepBump

/-- The activation under test. -/
def act (z : ℚ) : ℚ := 1 / 2 + z / (1 + z ^ 2)

/-- Its derivative, `(1 - z²)/(1 + z²)²`, negative for `|z| > 1`. -/
def act' (z : ℚ) : ℚ := (1 - z ^ 2) / (1 + z ^ 2) ^ 2

def forwardWithB (r : ℚ → ℚ) (θ : Matr 1 P ℚ) (v : Fin 4 → ℚ) : Fwd :=
  let z1 : Fin 4 → ℚ := fun h =>
    r ((List.finRange 4).foldl (fun s i => s + w1 θ h i * v i) 0)
  let u : Fin 5 → ℚ := Fin.lastCases 1 (fun h => r (act (z1 h)))
  let z2 : Fin 2 → ℚ := fun o =>
    r ((List.finRange 5).foldl (fun s j => s + w2 θ o j * u j) 0)
  ⟨z1, u, z2, fun o => r (act (z2 o))⟩

def forwardB : Matr 1 P ℚ → (Fin 4 → ℚ) → Fwd := forwardWithB id

def lossB (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) : ℚ :=
  ∑ p, let (x, y, c) := pattern p
       let f := forwardB θ (input x y c)
       let t := fullAdder x y c
       (cnt p : ℚ) * ((f.out 0 - boolQ t.1) ^ 2 + (f.out 1 - boolQ t.2) ^ 2) / 2

/-- Same backpropagation as `gradArr`, with `act'` in the hidden layer. -/
def gradArrB (r : ℚ → ℚ) (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) : Array ℚ := Id.run do
  let mut g : Array ℚ := Array.replicate P 0
  for p in List.finRange 8 do
    let (x, y, c) := pattern p
    let v := input x y c
    let f := forwardWithB r θ v
    let t := fullAdder x y c
    let n : ℚ := cnt p
    let d2 : Fin 2 → ℚ := ![r (n * (f.out 0 - boolQ t.1)), r (n * (f.out 1 - boolQ t.2))]
    for o in List.finRange 2 do
      for j in List.finRange 5 do
        let k := 16 + o.val * 5 + j.val
        g := g.modify k (· + r (d2 o * f.u j))
    for h in List.finRange 4 do
      let back := d2 0 * w2 θ 0 h.castSucc + d2 1 * w2 θ 1 h.castSucc
      let d1 := r (back * act' (f.z1 h))
      for i in List.finRange 4 do
        let k := h.val * 4 + i.val
        g := g.modify k (· + d1 * v i)
  return g

def cellOfB (θ : Matr 1 P ℚ) : Cell := fun x y c =>
  let f := forwardB θ (input x y c)
  (decide (1 / 2 < f.out 0), decide (1 / 2 < f.out 1))

def certificateB (θ : Matr 1 P ℚ) : Bool :=
  (List.finRange 8).all fun p =>
    let (x, y, c) := pattern p
    cellOfB θ x y c == fullAdder x y c

theorem certB_sound {θ : Matr 1 P ℚ} (h : certificateB θ = true) (x y c : Bool) :
    cellOfB θ x y c = fullAdder x y c := by
  have hp : ∀ p : Fin 8, cellOfB θ (pattern p).1 (pattern p).2.1 (pattern p).2.2
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

theorem learnedB_adds {θ : Matr 1 P ℚ} (h : certificateB θ = true) (a b : UInt32) :
    runAdder (cellOfB θ) a b = a + b :=
  serial_correct _ (certB_sound h) a b

/-- Existence on the step-16 grid (values -32, -16, 0, 16, 32) with this activation, found on the
first restart by `tools/existence/search_grid.py --act bump`. Index `= (v + 32) / 16`. As with
softsign, the step-32 grid has none (`tools/existence/exhaustive_32.py bump`). -/
def found16B : Array ℕ :=
  #[1, 3, 4, 1,  0, 1, 0, 4,  0, 1, 1, 4,  3, 3, 0, 2,
    3, 2, 2, 3, 1,  2, 0, 1, 1, 4]

theorem found16B_certified :
    certificateB ((gridOf 4).embedM (ofArr (gridOf 4) found16B)) = true := by
  decide +kernel

def stepArrB (g : Grid) (η : ℚ) (cnt : Fin 8 → ℕ) (a : Array ℕ) : Array ℕ :=
  stepCore g η a (gradArrB fx cnt (g.embedM (ofArr g a)))

/-- `runOne` with the new activation. -/
def runOneB (g : Grid) (a₀ : Array ℕ) (T : ℕ) : String := Id.run do
  let η : ℚ := 1 / 512
  let mut a := a₀
  let mut recent : List (Array ℕ) := []
  let mut curve : Array String := #[]
  for t in List.range (T + 1) do
    let θ := g.embedM (ofArr g a)
    let l := qf (lossB cnt θ / 2048)
    if t % 20 == 0 then curve := curve.push ("[" ++ toString t ++ "," ++ toString l ++ "]")
    if certificateB θ then
      return "{\"outcome\":\"certified\",\"at\":" ++ toString t ++ ",\"loss\":" ++ toString l
        ++ ",\"curve\":" ++ jlist curve.toList ++ "}"
    if t == T then break
    let a' := stepArrB g η cnt a
    if a' == a then
      return "{\"outcome\":\"stalled\",\"at\":" ++ toString t ++ ",\"loss\":" ++ toString l
        ++ ",\"curve\":" ++ jlist curve.toList ++ "}"
    match recent.findIdx? (· == a') with
    | some i =>
      return "{\"outcome\":\"cycle\",\"period\":" ++ toString (i + 2) ++ ",\"at\":" ++ toString t
        ++ ",\"loss\":" ++ toString l ++ ",\"curve\":" ++ jlist curve.toList ++ "}"
    | none => pure ()
    recent := (a :: recent).take 8
    a := a'
  let l := qf (lossB cnt (g.embedM (ofArr g a)) / 2048)
  return "{\"outcome\":\"budget\",\"at\":" ++ toString T ++ ",\"loss\":" ++ toString l
    ++ ",\"curve\":" ++ jlist curve.toList ++ "}"

/-! ## Squared-error variant

The sweeps above use the output delta `out - target`, the exact gradient of a loss with no lower
bound that rewards growing output pre-activations. That suits a saturating activation, not this
one, whose output returns to `1/2` as `|z| → ∞`. The squared-error delta `(out - target)·σ'(z2)` is
the exact gradient of the bounded loss `lossB` (and of `loss` for softsign). -/

/-- Exact gradient of `lossB` (squared error) for the bump activation. -/
def gradArrBsq (r : ℚ → ℚ) (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) : Array ℚ := Id.run do
  let mut g : Array ℚ := Array.replicate P 0
  for p in List.finRange 8 do
    let (x, y, c) := pattern p
    let v := input x y c
    let f := forwardWithB r θ v
    let t := fullAdder x y c
    let n : ℚ := cnt p
    let d2 : Fin 2 → ℚ := ![r (n * (f.out 0 - boolQ t.1) * act' (f.z2 0)),
                            r (n * (f.out 1 - boolQ t.2) * act' (f.z2 1))]
    for o in List.finRange 2 do
      for j in List.finRange 5 do
        let k := 16 + o.val * 5 + j.val
        g := g.modify k (· + r (d2 o * f.u j))
    for h in List.finRange 4 do
      let back := d2 0 * w2 θ 0 h.castSucc + d2 1 * w2 θ 1 h.castSucc
      let d1 := r (back * act' (f.z1 h))
      for i in List.finRange 4 do
        let k := h.val * 4 + i.val
        g := g.modify k (· + d1 * v i)
  return g

/-- Exact gradient of `loss` (squared error) for softsign: the control. -/
def gradArrSsq (r : ℚ → ℚ) (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) : Array ℚ := Id.run do
  let mut g : Array ℚ := Array.replicate P 0
  for p in List.finRange 8 do
    let (x, y, c) := pattern p
    let v := input x y c
    let f := forwardWith r θ v
    let t := fullAdder x y c
    let n : ℚ := cnt p
    let d2 : Fin 2 → ℚ := ![r (n * (f.out 0 - boolQ t.1) * σ' (f.z2 0)),
                            r (n * (f.out 1 - boolQ t.2) * σ' (f.z2 1))]
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

/-- `runOne` with the loss, certificate and gradient passed in. Also records wrong bits, since
squared error alone is a poor progress measure for the bump activation. -/
def runWith (lossF : Matr 1 P ℚ → ℚ) (certF : Matr 1 P ℚ → Bool) (cellF : Matr 1 P ℚ → Cell)
    (gradF : Matr 1 P ℚ → Array ℚ) (g : Grid) (a₀ : Array ℕ) (T : ℕ) : String := Id.run do
  let η : ℚ := 1 / 512
  let wrong (θ : Matr 1 P ℚ) : ℕ := (List.finRange 8).foldl (fun acc p =>
    let (x, y, c) := pattern p
    let o := cellF θ x y c; let t := fullAdder x y c
    acc + (if o.1 != t.1 then 1 else 0) + (if o.2 != t.2 then 1 else 0)) 0
  let mut a := a₀
  let mut recent : List (Array ℕ) := []
  let mut curve : Array String := #[]
  let mut best := 16
  for t in List.range (T + 1) do
    let θ := g.embedM (ofArr g a)
    let l := qf (lossF θ / 2048)
    let wb := wrong θ
    if wb < best then best := wb
    if t % 20 == 0 then
      curve := curve.push ("[" ++ toString t ++ "," ++ toString l ++ "," ++ toString wb ++ "]")
    let tail := ",\"loss\":" ++ toString l ++ ",\"wrong\":" ++ toString wb ++ ",\"bestWrong\":"
      ++ toString best ++ ",\"curve\":" ++ jlist curve.toList ++ "}"
    if certF θ then return "{\"outcome\":\"certified\",\"at\":" ++ toString t ++ tail
    if t == T then return "{\"outcome\":\"budget\",\"at\":" ++ toString T ++ tail
    let a' := stepCore g η a (gradF θ)
    if a' == a then return "{\"outcome\":\"stalled\",\"at\":" ++ toString t ++ tail
    match recent.findIdx? (· == a') with
    | some i =>
      return "{\"outcome\":\"cycle\",\"period\":" ++ toString (i + 2) ++ ",\"at\":" ++ toString t ++ tail
    | none => pure ()
    recent := (a :: recent).take 8
    a := a'
  return "{\"outcome\":\"budget\",\"at\":" ++ toString T ++ "}"

-- `SQ_ACT=bump|softsign SQ_E=<e>`: squared-error sweep of the 10 seeds on grid step `2^e`.
#eval show IO Unit from do
  let some act ← IO.getEnv "SQ_ACT" | pure ()
  let some e := (← IO.getEnv "SQ_E").bind String.toInt? | pure ()
  let g := gridOf e
  let mut rows : Array String := #[]
  for seed in seeds do
    let a := toGrid g (initReal seed)
    let r ← pure <| if act == "bump"
      then runWith (lossB cnt) certificateB cellOfB (gradArrBsq fx cnt) g a 2000
      else runWith (loss cnt) certificate cellOf (gradArrSsq fx cnt) g a 2000
    rows := rows.push ("{\"seed\":" ++ toString seed ++ ",\"run\":" ++ r ++ "}")
    IO.FS.writeFile (outDir / s!"sq_{act}_e{e}.json")
      ("{\"act\":\"" ++ act ++ "\",\"e\":" ++ toString e ++ ",\"runs\":" ++ jlist rows.toList ++ "}")

#eval show IO Unit from do
  let grp := ((← IO.getEnv "BUMP_GROUP").bind String.toNat?).getD 99
  for e in groups.getD grp [] do
    let g := gridOf e
    let mut rows : Array String := #[]
    for seed in seeds do
      let r ← pure (runOneB g (toGrid g (initReal seed)) 2000)
      rows := rows.push ("{\"seed\":" ++ toString seed ++ ",\"run\":" ++ r ++ "}")
      IO.FS.writeFile (outDir / s!"bump_sweep_e{e}.json")
        ("{\"e\":" ++ toString e ++ ",\"runs\":" ++ jlist rows.toList ++ "}")

end SweepBump
