import LeanTestground.SweepHidden

/-!
# `2x/(1+x²)` in both layers

Both the hidden and the output layer use `r(z) = 2z/(1+z²)`, range `[-1, 1]`, with `r(±1) = ±1`.

* Targets are `±1` (`2t - 1` for a bit `t`), reached exactly at output pre-activation `±1`.
* A bit is read as `out > 0`. Since `r` is odd and positive exactly on `z > 0`, that is the same
  as `z2 > 0`, so `certificateR` and `learnedR_adds` work as in `BinaryAdder.lean`.
* Loss is squared error `Σ cnt · Σ_o (out_o - t_o)² / 2` with its exact gradient: bounded, with
  minimum 0 exactly at the targets.

Up to a linear change of the output weights this is the `½ + z/(1+z²)` network of `SweepBump.lean`
with squared error: `(r(z) - (2t-1))² = 4(bump(z) - t)²`. Only the parametrization, and therefore
the gradient scale and what the grid can represent, differ; hence two learning rates.

Same grids, seeds and starting weights as `Sweep.lean`. Not imported by the library. Run with
`RAT2_E=<e> RAT2_ETA=<denominator> [RAT2_N=<seeds>] lake env lean LeanTestground/SweepRat2.lean`.
-/

open BinAdd Sweep SweepBump SweepHidden

namespace SweepRat2

def r (z : ℚ) : ℚ := 2 * z / (1 + z ^ 2)
def r' (z : ℚ) : ℚ := 2 * (1 - z ^ 2) / (1 + z ^ 2) ^ 2

/-- Target in `{-1, 1}` for a bit. -/
def tgt (b : Bool) : ℚ := if b then 1 else -1

def forwardR (q : ℚ → ℚ) (θ : Matr 1 P ℚ) (v : Fin 4 → ℚ) : Fwd :=
  let z1 : Fin 4 → ℚ := fun h =>
    q ((List.finRange 4).foldl (fun s i => s + w1 θ h i * v i) 0)
  let u : Fin 5 → ℚ := Fin.lastCases 1 (fun h => q (r (z1 h)))
  let z2 : Fin 2 → ℚ := fun o =>
    q ((List.finRange 5).foldl (fun s j => s + w2 θ o j * u j) 0)
  ⟨z1, u, z2, fun o => q (r (z2 o))⟩

def lossR (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) : ℚ :=
  ∑ p, let (x, y, c) := pattern p
       let f := forwardR id θ (input x y c)
       let t := fullAdder x y c
       (cnt p : ℚ) * ((f.out 0 - tgt t.1) ^ 2 + (f.out 1 - tgt t.2) ^ 2) / 2

/-- Exact gradient of `lossR` (squared error), computed into an array once. -/
def gradArrR (q : ℚ → ℚ) (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) : Array ℚ := Id.run do
  let mut g : Array ℚ := Array.replicate P 0
  for p in List.finRange 8 do
    let (x, y, c) := pattern p
    let v := input x y c
    let f := forwardR q θ v
    let t := fullAdder x y c
    let n : ℚ := cnt p
    let d2 : Fin 2 → ℚ := ![q (n * (f.out 0 - tgt t.1) * r' (f.z2 0)),
                            q (n * (f.out 1 - tgt t.2) * r' (f.z2 1))]
    for o in List.finRange 2 do
      for j in List.finRange 5 do
        let k := 16 + o.val * 5 + j.val
        g := g.modify k (· + q (d2 o * f.u j))
    for h in List.finRange 4 do
      let back := d2 0 * w2 θ 0 h.castSucc + d2 1 * w2 θ 1 h.castSucc
      let d1 := q (back * r' (f.z1 h))
      for i in List.finRange 4 do
        let k := h.val * 4 + i.val
        g := g.modify k (· + d1 * v i)
  return g

def cellOfR (θ : Matr 1 P ℚ) : Cell := fun x y c =>
  let f := forwardR id θ (input x y c)
  (decide (0 < f.out 0), decide (0 < f.out 1))

def certificateR (θ : Matr 1 P ℚ) : Bool :=
  (List.finRange 8).all fun p =>
    let (x, y, c) := pattern p
    cellOfR θ x y c == fullAdder x y c

theorem certR_sound {θ : Matr 1 P ℚ} (h : certificateR θ = true) (x y c : Bool) :
    cellOfR θ x y c = fullAdder x y c := by
  have hp : ∀ p : Fin 8, cellOfR θ (pattern p).1 (pattern p).2.1 (pattern p).2.2
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

/-- Weights passing `certificateR` add every pair of u32. -/
theorem learnedR_adds {θ : Matr 1 P ℚ} (h : certificateR θ = true) (a b : UInt32) :
    runAdder (cellOfR θ) a b = a + b :=
  serial_correct _ (certR_sound h) a b

/-- Existence on the step-16 grid (values -32, -16, 0, 16, 32), found on the first restart by
`tools/existence/search_grid.py --act rat2`. Index `= (v + 32) / 16`. -/
def found16R : Array ℕ :=
  #[3, 0, 1, 3,  0, 2, 0, 4,  3, 4, 3, 0,  3, 4, 3, 0,
    0, 1, 1, 0, 2,  2, 0, 4, 4, 2]

theorem found16R_certified :
    certificateR ((gridOf 4).embedM (ofArr (gridOf 4) found16R)) = true := by
  decide +kernel

/-- Train until certified, stalled, cycling (period ≤ 8) or out of budget, with learning rate `η`.
Records squared error and wrong bits every 20 steps, and the fewest wrong bits ever reached. -/
def runR (g : Grid) (η : ℚ) (a₀ : Array ℕ) (T : ℕ) : String := Id.run do
  let wrong (θ : Matr 1 P ℚ) : ℕ := (List.finRange 8).foldl (fun acc p =>
    let (x, y, c) := pattern p
    let o := cellOfR θ x y c; let t := fullAdder x y c
    acc + (if o.1 != t.1 then 1 else 0) + (if o.2 != t.2 then 1 else 0)) 0
  let mut a := a₀
  let mut recent : List (Array ℕ) := []
  let mut curve : Array String := #[]
  let mut best := 16
  for t in List.range (T + 1) do
    let θ := g.embedM (ofArr g a)
    let l := qf (lossR cnt θ / 2048)
    let wb := wrong θ
    if wb < best then best := wb
    if t % 20 == 0 then
      curve := curve.push ("[" ++ toString t ++ "," ++ toString l ++ "," ++ toString wb ++ "]")
    let tail := ",\"loss\":" ++ toString l ++ ",\"wrong\":" ++ toString wb ++ ",\"bestWrong\":"
      ++ toString best ++ ",\"curve\":" ++ jlist curve.toList ++ "}"
    if certificateR θ then return "{\"outcome\":\"certified\",\"at\":" ++ toString t ++ tail
    if t == T then return "{\"outcome\":\"budget\",\"at\":" ++ toString T ++ tail
    let a' := stepCore g η a (gradArrR fx cnt θ)
    if a' == a then return "{\"outcome\":\"stalled\",\"at\":" ++ toString t ++ tail
    match recent.findIdx? (· == a') with
    | some i =>
      return "{\"outcome\":\"cycle\",\"period\":" ++ toString (i + 2) ++ ",\"at\":" ++ toString t ++ tail
    | none => pure ()
    recent := (a :: recent).take 8
    a := a'
  return "{\"outcome\":\"budget\",\"at\":" ++ toString T ++ "}"

#eval show IO Unit from do
  let some e := (← IO.getEnv "RAT2_E").bind String.toInt? | pure ()
  let some den := (← IO.getEnv "RAT2_ETA").bind String.toNat? | pure ()
  let n := ((← IO.getEnv "RAT2_N").bind String.toNat?).getD 10
  let g := gridOf e
  let η : ℚ := 1 / den
  let mut rows : Array String := #[]
  for seed in seeds.take n do
    let run ← pure (runR g η (toGrid g (initReal seed)) 2000)
    rows := rows.push ("{\"seed\":" ++ toString seed ++ ",\"run\":" ++ run ++ "}")
    IO.FS.writeFile (outDir / s!"rat2_e{e}_eta{den}.json")
      ("{\"e\":" ++ toString e ++ ",\"eta\":" ++ toString den ++ ",\"runs\":" ++ jlist rows.toList ++ "}")

end SweepRat2
