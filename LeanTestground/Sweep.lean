import LeanTestground.BinaryAdder

/-!
# Existence versus trainability across grid steps

For each grid step `s = 2^e` on `[-32, 32]` (same data, `η = 1/512`):

* **trainability**: 10 seeds. Each seed draws real starting weights once (multiples of 1/1024
  in `[-1/2, 1/2]`) and rounds them onto every grid, so runs are paired across grids. A run
  stops when the certificate passes, at a fixed point (`stall_of_fixed`), on a cycle of
  period ≤ 8, or after 2000 steps.
* **existence**: certified weights on the step-4, step-8 and step-16 grids
  (`hand4_certified`, `hand8_certified`, `found16_certified`), hence on every finer grid of the
  same range; none on the step-32 grid (exhaustive search, `tools/existence/exhaustive_32.py`).

Not imported by the library. Run a group of grids with
`SWEEP_GROUP=<n> lake env lean LeanTestground/Sweep.lean`, or log full trajectories of all
seeds on one grid with `SWEEP_TRACE=<e> lake env lean LeanTestground/Sweep.lean`
(grid step `2^e`, e.g. `-4` for 1/16).
-/

open BinAdd

namespace Sweep

def outDir : System.FilePath :=
  "C:/Users/WRETCH~1/AppData/Local/Temp/claude/E--Code-lean-testground/2def189c-5d25-471f-b691-4b7a1bd6c516/scratchpad"

/-- Grid of step `2^e` on `[-32, 32]`. -/
def gridOf (e : ℤ) : Grid :=
  if 0 ≤ e then ⟨-32, 2 ^ e.toNat, 64 / 2 ^ e.toNat, by positivity⟩
  else ⟨-32, 1 / 2 ^ (-e).toNat, 64 * 2 ^ (-e).toNat, by positivity⟩

/-! ## Existence: a certified solution on the step-4 grid -/

/-- Hand-built weights (all multiples of 4): hidden unit `k` fires when `x+y+c ≥ k`
(`z = 8(x+y+c) - 8k + 4`), sum `= h1 - h2 + h3`, carry `= h2`. As indices of the step-4 grid. -/
def hand4 : Array ℕ :=
  -- value v ↦ index (v + 32) / 4
  #[10, 10, 10, 7,  10, 10, 10, 5,  10, 10, 10, 3,  8, 8, 8, 8,
    10, 6, 10, 8, 7,  8, 10, 8, 8, 7]

theorem hand4_certified : certificate ((gridOf 2).embedM (ofArr (gridOf 2) hand4)) = true := by
  decide +kernel

/-- Step 8 (values -32, -24, …, 32), built by hand: `A = σ(16n - 8)` (n ≥ 1),
`B = σ(16n - 24)` (n ≥ 2), `C = σ(8n - 24)` (≈ ½ only at n = 3); sum `= 16A - 16B + 32C - 8`,
carry `= 16B - 8`. Index `= (v + 32) / 8`. -/
def hand8 : Array ℕ :=
  #[6, 6, 6, 3,  6, 6, 6, 1,  5, 5, 5, 1,  4, 4, 4, 4,
    6, 2, 8, 4, 3,  4, 6, 4, 4, 3]

theorem hand8_certified : certificate ((gridOf 3).embedM (ofArr (gridOf 3) hand8)) = true := by
  decide +kernel

/-- Step 16 (values -32, -16, 0, 16, 32), found by randomized search (`tools/existence/search_16.py`).
Index `= (v + 32) / 16`. -/
def found16 : Array ℕ :=
  #[0, 4, 3, 1,  0, 1, 2, 3,  4, 0, 3, 2,  4, 3, 4, 0,
    4, 1, 4, 1, 1,  2, 0, 1, 4, 2]

theorem found16_certified : certificate ((gridOf 4).embedM (ofArr (gridOf 4) found16)) = true := by
  decide +kernel

/-! Step 32 (values -32, 0, 32): no certified weights exist. Checked exhaustively outside Lean
(`tools/existence/exhaustive_32.py`): all 1 929 501 multisets of 4 distinct hidden units against all 243
output weight vectors, requiring every output pre-activation to clear 10⁻⁹. -/

/-! ## Trainability -/

/-- Real starting weights for a seed: multiples of 1/1024 in `[-1/2, 1/2]`. -/
def initReal (seed : UInt32) : Array ℚ := Id.run do
  let mut s := seed
  let mut a : Array ℚ := #[]
  for _ in List.range P do
    s := lcg s
    let off : ℤ := ((s >>> 8).toNat % 1025 : ℕ)
    a := a.push (((off - 512 : ℤ) : ℚ) / 1024)
  return a

def toGrid (g : Grid) (a : Array ℚ) : Array ℕ := a.map fun q => (g.round q).val

def jlist (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

/-- Train until certified, stalled, cycling (period ≤ 8) or out of budget. -/
def runOne (g : Grid) (a₀ : Array ℕ) (T : ℕ) : String := Id.run do
  let mut a := a₀
  let mut recent : List (Array ℕ) := []
  let mut curve : Array String := #[]
  for t in List.range (T + 1) do
    let θ := g.embedM (ofArr g a)
    let l := qf (loss cnt θ / 2048)
    if t % 20 == 0 then curve := curve.push ("[" ++ toString t ++ "," ++ toString l ++ "]")
    if certificate θ then
      return "{\"outcome\":\"certified\",\"at\":" ++ toString t ++ ",\"loss\":" ++ toString l
        ++ ",\"curve\":" ++ jlist curve.toList ++ "}"
    if t == T then break
    let a' := stepArr g η₀ cnt a
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
  let l := qf (loss cnt (g.embedM (ofArr g a)) / 2048)
  return "{\"outcome\":\"budget\",\"at\":" ++ toString T ++ ",\"loss\":" ++ toString l
    ++ ",\"curve\":" ++ jlist curve.toList ++ "}"
where η₀ : ℚ := 1 / 512

def seeds : List UInt32 := [7, 1, 2, 3, 4, 5, 6, 8, 9, 10]

def groups : List (List ℤ) := [[2, 1, 0, -1, -2, -8], [-3, -7], [-4, -6], [-5]]

#eval show IO Unit from do
  let grp := ((← IO.getEnv "SWEEP_GROUP").bind String.toNat?).getD 99
  for e in groups.getD grp [] do
    let g := gridOf e
    let mut rows : Array String := #[]
    for seed in seeds do
      let r ← pure (runOne g (toGrid g (initReal seed)) 2000)
      rows := rows.push ("{\"seed\":" ++ toString seed ++ ",\"run\":" ++ r ++ "}")
      IO.FS.writeFile (outDir / s!"sweep_e{e}.json")
        ("{\"e\":" ++ toString e ++ ",\"runs\":" ++ jlist rows.toList ++ "}")
      IO.println s!"e={e} seed={seed} done"

/-! ## Full trajectories on one grid -/

/-- Train from `a₀` for up to `T` steps, logging every `every` steps: error, wrong bits,
hidden pre-activations for all 8 patterns, weights, and the fixed-point gradient. -/
def traceOne (g : Grid) (a₀ : Array ℕ) (T every : ℕ) : String := Id.run do
  let η : ℚ := 1 / 512
  let mut a := a₀
  let mut recs : Array String := #[]
  let mut ending := "budget"
  for t in List.range (T + 1) do
    let θ := g.embedM (ofArr g a)
    let G := gradArr fx cnt θ
    let cert := certificate θ
    let a' := stepCore g η a G
    let last := cert || a' == a || t == T
    if t % every == 0 || last then
      let fs := (List.finRange 8).map fun p =>
        let (x, y, c) := pattern p
        forward θ (input x y c)
      let outs := fs.flatMap fun f => [qf (f.out 0), qf (f.out 1)]
      let z1s := fs.flatMap fun f => (List.finRange 4).map fun h => qf (f.z1 h)
      let ws := (List.finRange P).map fun j => qf (θ 0 j)
      let gs := (List.range P).map fun j => qf (G.getD j 0 / 2048)
      recs := recs.push ("{\"t\":" ++ toString t ++ ",\"loss\":" ++ toString (qf (loss cnt θ / 2048))
        ++ ",\"out\":" ++ jlist (outs.map toString) ++ ",\"z1\":" ++ jlist (z1s.map toString)
        ++ ",\"w\":" ++ jlist (ws.map toString) ++ ",\"g\":" ++ jlist (gs.map toString) ++ "}")
    if cert then ending := "certified"; break
    if a' == a then ending := "stalled"; break
    a := a'
  return "{\"ending\":\"" ++ ending ++ "\",\"records\":" ++ jlist recs.toList ++ "}"

#eval show IO Unit from do
  match (← IO.getEnv "SWEEP_TRACE").bind String.toInt? with
  | none => pure ()
  | some e =>
    let g := gridOf e
    let mut rows : Array String := #[]
    for seed in seeds do
      let r ← pure (traceOne g (toGrid g (initReal seed)) 2000 5)
      rows := rows.push ("{\"seed\":" ++ toString seed ++ ",\"trace\":" ++ r ++ "}")
      IO.FS.writeFile (outDir / s!"trace_e{e}.json")
        ("{\"e\":" ++ toString e ++ ",\"half\":" ++ toString (qf g.half) ++ ",\"runs\":" ++ jlist rows.toList ++ "}")

end Sweep
