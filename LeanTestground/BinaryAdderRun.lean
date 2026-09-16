import LeanTestground.BinaryAdder

/-!
# Experiments for `BinaryAdder.lean`

Not imported by the library, so `lake build` does not retrain. Run with
`lake env lean LeanTestground/BinaryAdderRun.lean`.
-/

open BinAdd

#eval (List.finRange 8).map cnt

-- Reproduces `learned` and certifies at step 825.
#eval timeit "fine" (report "grid step 1/64, η=1/512" gFine (1/512) a0 2000 25)
#eval (trace gFine (1/512) a0 2000 25).2.1 == learned

-- Same range and seed, coarser grids.
def gMid : Grid := ⟨-32, 1 / 8, 512, by norm_num⟩
def gCoarse : Grid := ⟨-32, 1 / 2, 128, by norm_num⟩
#eval timeit "mid" (report "grid step 1/8, η=1/512" gMid (1/512) (initArr gMid 4 7) 2000 25)
#eval timeit "coarse" (report "grid step 1/2, η=1/512" gCoarse (1/512) (initArr gCoarse 1 7) 2000 25)

/-- Hand-built weights on the coarse grid (step 1/2): hidden unit `k` fires when
`x + y + c ≥ k` (`z = 8(x+y+c) - 8k + 4`), sum `= h1 - h2 + h3`, carry `= h2`. Training on this
grid never finds them, but they exist: representable is not the same as trainable. -/
def handCoarse : Array ℕ :=
  #[80, 80, 80, 56,  80, 80, 80, 40,  80, 80, 80, 24,  64, 64, 64, 64,
    80, 48, 80, 64, 56,  64, 80, 64, 64, 56]

theorem handCoarse_certified : certificate (gCoarse.embedM (ofArr gCoarse handCoarse)) = true := by
  decide +kernel

theorem handCoarse_adds (a b : UInt32) :
    runAdder (cellOf (gCoarse.embedM (ofArr gCoarse handCoarse))) a b = a + b :=
  learned_adds handCoarse_certified a b

-- squared error of the hand-built weights (≈ 0.0153)
#eval qf (loss cnt (gCoarse.embedM (ofArr gCoarse handCoarse)) / 2048)

#print axioms trained_net_adds
#print axioms handCoarse_adds
#print axioms stall_of_fixed
