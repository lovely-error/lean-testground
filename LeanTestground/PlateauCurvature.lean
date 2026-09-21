import LeanTestground.BinaryAdder

/-!
# The plateau is a saddle, checked in exact arithmetic

The instrumented run of `PlateauAnalysis.lean` (grid step 1/64, seed 7, η = 1/512) sits on a
plateau at one wrong bit from about step 150 to step 790. `a600` is its weight state at step 600,
as grid indices, reproduced by

    #eval (iterf 600 (stepArr gFine (1/512) cnt) a0).toList

Training there follows `θ ← θ - η·g`, where `g = gradArr fx cnt θ` is the gradient of the loss
`Σ cnt · Σ_o ∫ (σ - target)`. Along a direction `v`, that loss curves like

    q(t) = (g(θ + t·v) - g(θ - t·v)) · v / (2t),

a finite-difference Rayleigh quotient, and `q < 0` means the loss curves *downward* along `v`: the
state is not a local minimum, and gradient descent expands along `v` (the escape from the plateau)
rather than contracting. Everything here is exact `ℚ` arithmetic, so `decide` settles it.

`v` is a rational approximation (multiples of 1/256) of the eigenvector of the smallest Hessian
eigenvalue at this state, computed in floating point in `scratchpad/hessian_plateau.py`; the proof
does not depend on where it came from. Its largest components are the sum←h3 output weight
(index 19) and h3's input weights and bias (indices 12–15), which is the pair of changes the
plateau analysis identified as the escape.

Not imported by the library. Run with `lake env lean LeanTestground/PlateauCurvature.lean`.
-/

open BinAdd

namespace PlateauCurvature

/-- Grid indices of the step-600 state of the plateau run. -/
def a600 : Array ℕ :=
  #[2694, 2679, 2714, 1196, 1693, 1706, 1676, 2551, 2370, 2393, 2338, 1876, 1764,
    1777, 1748, 2465, 1089, 2124, 3495, 2035, 1515, 3745, 288, 2759, 436, 2003]

def θ600 : Matr 1 P ℚ := gFine.embedM (ofArr gFine a600)

/-- The candidate escape direction, in multiples of 1/256. -/
def vnum : Array ℤ :=
  #[3, 2, 3, -4, -27, -29, -26, 19, 1, 2, 0, 3, 53, 57, 48, -25, -25, 127, 0, -188, 36, 9, -5, 7, 19, 8]

def v (j : ℕ) : ℚ := (vnum.getD j 0 : ℚ) / 256

def shift (t : ℚ) : Matr 1 P ℚ := fun _ j => θ600 0 j + t * v j

/-- Finite-difference curvature of the training loss along `v`, at scale `t`. -/
def rayleigh (t : ℚ) : ℚ :=
  let gp := gradArr id cnt (shift t)
  let gm := gradArr id cnt (shift (-t))
  ((List.range P).map fun j => (gp.getD j 0 - gm.getD j 0) * v j).sum / (2 * t)

/-- **The plateau state has a direction of negative curvature.** So it is not a local minimum:
the run is passing a saddle, and gradient descent grows along `v`. -/
theorem plateau_negative_curvature : rayleigh (1 / 1024) < 0 := by
  decide +kernel

/-- The same at a coarser scale, so the sign is not an artefact of the step size. -/
theorem plateau_negative_curvature' : rayleigh (1 / 256) < 0 := by
  decide +kernel

end PlateauCurvature

#eval (PlateauCurvature.rayleigh (1 / 1024) : ℚ) |> BinAdd.qf   -- ≈ -1.67
#eval BinAdd.certificate PlateauCurvature.θ600                  -- false: still one bit wrong
