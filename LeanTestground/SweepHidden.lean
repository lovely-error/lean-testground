import LeanTestground.SweepBump

/-!
# Changing only the hidden-layer activation

The output layer stays as in `BinaryAdder.lean`: softsign `σ` with output delta `out - target`,
the best-performing combination so far. Only the hidden activation `hact` changes:

* `relu`  : `max 0 z`, monotone, unbounded, not saturating
* `rat2`  : `2z/(1+z²)`, range `[-1, 1]`, peaks at `z = ±1`, tends to 0; the `bump` shape rescaled
* `bump`  : `1/2 + z/(1+z²)`, range `[0, 1]`; the control for `rat2`
* `soft`  : softsign `σ`, which reproduces the original sweep

Same grids, seeds, starting weights, `η = 1/512` and stopping rules as `Sweep.lean`. Each run also
reports hidden-unit diagnostics at the end: how many units are dead (`relu`: zero on all 8
patterns) and what share of pre-activations sit past the turning point `|z| > 1` (`rat2`, `bump`).

Not imported by the library. Run with
`HID_ACT=<relu|rat2|bump|soft> HID_E=<e> [HID_N=<seeds>] lake env lean LeanTestground/SweepHidden.lean`.
-/

open BinAdd Sweep SweepBump

namespace SweepHidden

structure HAct where
  f : ℚ → ℚ
  df : ℚ → ℚ

def relu : HAct := ⟨fun z => max 0 z, fun z => if 0 < z then 1 else 0⟩
def rat2 : HAct := ⟨fun z => 2 * z / (1 + z ^ 2), fun z => 2 * (1 - z ^ 2) / (1 + z ^ 2) ^ 2⟩
def bumpH : HAct := ⟨act, act'⟩
def softH : HAct := ⟨σ, σ'⟩

def actOf : String → Option HAct
  | "relu" => some relu | "rat2" => some rat2 | "bump" => some bumpH | "soft" => some softH
  | _ => none

def forwardH (A : HAct) (r : ℚ → ℚ) (θ : Matr 1 P ℚ) (v : Fin 4 → ℚ) : Fwd :=
  let z1 : Fin 4 → ℚ := fun h =>
    r ((List.finRange 4).foldl (fun s i => s + w1 θ h i * v i) 0)
  let u : Fin 5 → ℚ := Fin.lastCases 1 (fun h => r (A.f (z1 h)))
  let z2 : Fin 2 → ℚ := fun o =>
    r ((List.finRange 5).foldl (fun s j => s + w2 θ o j * u j) 0)
  ⟨z1, u, z2, fun o => r (σ (z2 o))⟩

def lossH (A : HAct) (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) : ℚ :=
  ∑ p, let (x, y, c) := pattern p
       let f := forwardH A id θ (input x y c)
       let t := fullAdder x y c
       (cnt p : ℚ) * ((f.out 0 - boolQ t.1) ^ 2 + (f.out 1 - boolQ t.2) ^ 2) / 2

/-- Backpropagation with output delta `out - target` and `A.df` in the hidden layer. -/
def gradArrH (A : HAct) (r : ℚ → ℚ) (cnt : Fin 8 → ℕ) (θ : Matr 1 P ℚ) : Array ℚ := Id.run do
  let mut g : Array ℚ := Array.replicate P 0
  for p in List.finRange 8 do
    let (x, y, c) := pattern p
    let v := input x y c
    let f := forwardH A r θ v
    let t := fullAdder x y c
    let n : ℚ := cnt p
    let d2 : Fin 2 → ℚ := ![r (n * (f.out 0 - boolQ t.1)), r (n * (f.out 1 - boolQ t.2))]
    for o in List.finRange 2 do
      for j in List.finRange 5 do
        let k := 16 + o.val * 5 + j.val
        g := g.modify k (· + r (d2 o * f.u j))
    for h in List.finRange 4 do
      let back := d2 0 * w2 θ 0 h.castSucc + d2 1 * w2 θ 1 h.castSucc
      let d1 := r (back * A.df (f.z1 h))
      for i in List.finRange 4 do
        let k := h.val * 4 + i.val
        g := g.modify k (· + d1 * v i)
  return g

def cellOfH (A : HAct) (θ : Matr 1 P ℚ) : Cell := fun x y c =>
  let f := forwardH A id θ (input x y c)
  (decide (1 / 2 < f.out 0), decide (1 / 2 < f.out 1))

def certificateH (A : HAct) (θ : Matr 1 P ℚ) : Bool :=
  (List.finRange 8).all fun p =>
    let (x, y, c) := pattern p
    cellOfH A θ x y c == fullAdder x y c

theorem certH_sound {A : HAct} {θ : Matr 1 P ℚ} (h : certificateH A θ = true) (x y c : Bool) :
    cellOfH A θ x y c = fullAdder x y c := by
  have hp : ∀ p : Fin 8, cellOfH A θ (pattern p).1 (pattern p).2.1 (pattern p).2.2
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

/-- Any hidden activation: weights passing the certificate add every pair of u32. -/
theorem learnedH_adds {A : HAct} {θ : Matr 1 P ℚ} (h : certificateH A θ = true) (a b : UInt32) :
    runAdder (cellOfH A θ) a b = a + b :=
  serial_correct _ (certH_sound h) a b

/-! ## Existence for ReLU hidden units

`h0 = relu(n)`, `h1 = relu(n - 1)`, `h2 = relu(n - 2)` with `n = x + y + c`. Then
`n - 2·relu(n-1) + 2·relu(n-2) = 0, 1, 0, 1` and `relu(n-1) - relu(n-2) = 0, 0, 1, 1`, so
sum `= 2h0 - 4h1 + 4h2 - 1` and carry `= 2h1 - 2h2 - 1` have output pre-activations ±1 of the
right sign. All weights are integers, so this lies on the step-1 grid and every finer one,
including the 1/16 and 1/128 grids used below. Index `= v + 32`. -/
def reluStep1 : Array ℕ :=
  #[33, 33, 33, 32,  33, 33, 33, 31,  33, 33, 33, 30,  32, 32, 32, 32,
    34, 28, 36, 32, 31,  32, 34, 30, 32, 31]

theorem reluStep1_certified :
    certificateH relu ((gridOf 0).embedM (ofArr (gridOf 0) reluStep1)) = true := by
  decide +kernel

/-! ## Runs -/

def toF (q : ℚ) : Float := Float.ofInt ⌊q * 2 ^ 40⌋ / 1099511627776.0

/-- End-of-run hidden diagnostics: dead ReLU units, and the share of hidden pre-activations past
`|z| > 1`, over all 8 patterns. -/
def hiddenDiag (A : HAct) (θ : Matr 1 P ℚ) : String :=
  let zs := (List.finRange 8).map fun p =>
    let (x, y, c) := pattern p
    (forwardH A id θ (input x y c)).z1
  let dead := (List.finRange 4).filter (fun h => zs.all fun z => z h ≤ 0) |>.length
  let past := (zs.flatMap fun z => (List.finRange 4).map z).filter (fun v => 1 < |v|) |>.length
  let maxAbs := (zs.flatMap fun z => (List.finRange 4).map fun h => toF |z h|).foldl
    (fun m v => if m < v then v else m) 0.0
  "\"deadRelu\":" ++ toString dead ++ ",\"pastTurn\":" ++ toString past ++ ",\"maxAbsZ1\":" ++ toString maxAbs

#eval show IO Unit from do
  let some name ← IO.getEnv "HID_ACT" | pure ()
  let some A := actOf name | IO.println s!"unknown HID_ACT {name}"
  let some e := (← IO.getEnv "HID_E").bind String.toInt? | pure ()
  let n := ((← IO.getEnv "HID_N").bind String.toNat?).getD 10
  let g := gridOf e
  let mut rows : Array String := #[]
  for seed in seeds.take n do
    let a := toGrid g (initReal seed)
    let r ← pure (runWith (lossH A cnt) (certificateH A) (cellOfH A) (gradArrH A fx cnt) g a 2000)
    -- re-run to the same end state for diagnostics (deterministic)
    let endState ← pure <| Id.run do
      let mut b := a
      let mut recent : List (Array ℕ) := []
      for _ in List.range 2000 do
        let θ := g.embedM (ofArr g b)
        if certificateH A θ then break
        let b' := stepCore g (1 / 512) b (gradArrH A fx cnt θ)
        if b' == b || recent.contains b' then break
        recent := (b :: recent).take 8
        b := b'
      return b
    let diag := hiddenDiag A (g.embedM (ofArr g endState))
    rows := rows.push ("{\"seed\":" ++ toString seed ++ ",\"diag\":{" ++ diag ++ "},\"run\":" ++ r ++ "}")
    IO.FS.writeFile (outDir / s!"hid_{name}_e{e}.json")
      ("{\"act\":\"" ++ name ++ "\",\"e\":" ++ toString e ++ ",\"runs\":" ++ jlist rows.toList ++ "}")

end SweepHidden
