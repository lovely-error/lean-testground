import LeanTestground.BinaryAdder

/-!
# Why does training plateau, then drop suddenly?

Instruments the step-1/64 run of `BinaryAdderRun.lean` (plateau near squared error 0.04
for steps ~300–775, then certified at 825) and writes JSON for plotting:

* `instrumented`: every 5 steps, all 8 patterns' outputs, all hidden pre-activations,
  all 26 weights, gradient norm, how many weights moved, how many updates the grid swallowed.
* `fine1024`: the same starting weights on a grid 16× finer (control: is the plateau a
  rounding artifact?).
* `seeds`: other random starts (control: is the plateau typical?).

Not imported by the library. Run with `lake env lean LeanTestground/PlateauAnalysis.lean`.
-/

open BinAdd

namespace Plateau

def outDir : System.FilePath :=
  "C:/Users/WRETCH~1/AppData/Local/Temp/claude/E--Code-lean-testground/2def189c-5d25-471f-b691-4b7a1bd6c516/scratchpad"

def fstr (x : Float) : String :=
  if x.isNaN || x.isInf then "null" else toString x

def jlist (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"
def jf (xs : List Float) : String := jlist (xs.map fstr)

/-- Train from `a₀`, logging everything every `every` steps. -/
def run (g : Grid) (η : ℚ) (a₀ : Array ℕ) (T every : ℕ) : String := Id.run do
  let mut a := a₀
  let mut recs : Array String := #[]
  let mut certAt : Option ℕ := none
  for t in List.range (T + 1) do
    let θ := g.embedM (ofArr g a)
    let G := gradArr fx cnt θ
    let a' := stepCore g η a G
    if certAt.isNone && certificate θ then certAt := some t
    if t % every == 0 then
      let moved := (List.range P).countP fun j => a'.getD j 0 != a.getD j 0
      let suppressed := (List.range P).countP fun j =>
        let u := η * G.getD j 0
        u != 0 && |u| < g.half
      let gn := Float.sqrt (qf ((G.foldl (fun s x => s + x * x) 0) / (2048 * 2048)))
      let fs := (List.finRange 8).map fun p =>
        let (x, y, c) := pattern p
        forward θ (input x y c)
      let outs := fs.flatMap fun f => [qf (f.out 0), qf (f.out 1)]
      let z1s := fs.flatMap fun f => (List.finRange 4).map fun h => qf (f.z1 h)
      let ws := (List.finRange P).map fun j => qf (θ 0 j)
      recs := recs.push ("{\"t\":" ++ toString t ++ ",\"loss\":" ++ fstr (qf (loss cnt θ / 2048))
        ++ ",\"gnorm\":" ++ fstr gn ++ ",\"moved\":" ++ toString moved
        ++ ",\"suppressed\":" ++ toString suppressed ++ ",\"out\":" ++ jf outs
        ++ ",\"z1\":" ++ jf z1s ++ ",\"w\":" ++ jf ws ++ "}")
    a := a'
  let cert := match certAt with | some t => toString t | none => "null"
  return "{\"certifiedAt\":" ++ cert ++ ",\"records\":" ++ jlist recs.toList ++ "}"

def gFine1024 : Grid := ⟨-32, 1 / 1024, 65536, by norm_num⟩

-- Already written; re-enable to regenerate.
/-
#eval timeit "instrumented 1/64" do
  let s ← pure (run gFine (1/512) a0 1000 5)
  IO.FS.writeFile (outDir / "plateau_fine64.json") s

-- Same real starting weights: index i on the 1/64 grid is index 16·i on the 1/1024 grid.
#eval timeit "instrumented 1/1024" do
  let s ← pure (run gFine1024 (1/512) (a0.map (· * 16)) 1500 5)
  IO.FS.writeFile (outDir / "plateau_fine1024.json") s

-/

def seedJson (seed : UInt32) : String :=
  let (tr, _, res) := trace gFine (1/512) (initArr gFine 32 seed) 2000 10
  let (kind, at_) := match res with
    | .certified t => ("certified", toString t)
    | .stalled t => ("stalled", toString t)
    | .budget => ("budget", "null")
  "{\"seed\":" ++ toString seed ++ ",\"outcome\":\"" ++ kind ++ "\",\"at\":" ++ at_
    ++ ",\"curve\":" ++ jlist (tr.map fun (t, l) => "[" ++ toString t ++ "," ++ fstr l ++ "]") ++ "}"

/-
#eval timeit "seeds" do
  let mut out : Array String := #[]
  for seed in [7, 1, 2, 3, 4, 5] do
    let s ← pure (seedJson seed)
    out := out.push s
    IO.FS.writeFile (outDir / "plateau_seeds.json") (jlist out.toList)
-/

end Plateau

namespace Plateau

/-! ## Control: do the seeds that stall on the 1/64 grid escape on the 1/1024 grid? -/

#eval timeit "stalled seeds, both grids" do
  for seed in [2, 3] do
    let a := initArr gFine 32 seed
    let s64 ← pure (run gFine (1/512) a 1400 10)
    IO.FS.writeFile (outDir / s!"seed{seed}_fine64.json") s64
    let s1024 ← pure (run gFine1024 (1/512) (a.map (· * 16)) 1400 10)
    IO.FS.writeFile (outDir / s!"seed{seed}_fine1024.json") s1024

end Plateau
