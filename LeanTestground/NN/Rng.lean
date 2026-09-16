/-!
# A small deterministic PRNG

`xorshift64*`: one multiply on top of a 3-shift xorshift. Not cryptographic and
not meant to be -- it needs only to be reproducible from a seed and free of the
short-period artifacts that would show up as visible structure in the initial
weights.

The state is threaded explicitly rather than hidden in a monad, because weight
initialisation and sampling both want to be pure functions of a seed.
-/

namespace TinyLM

structure Rng where
  s : UInt64
  deriving Inhabited

namespace Rng

/-- Seed the generator. The state must be non-zero for xorshift to work at all,
so the seed is mixed and then forced away from zero. (Named `seed` rather than
`mk`, which the structure constructor already takes.) -/
def seed (seed : UInt64) : Rng :=
  let x := seed ^^^ 0x9E3779B97F4A7C15
  ⟨if x == 0 then 0x853C49E6748FEA9B else x⟩

/-- Next raw 64-bit word. -/
@[inline] def nextU64 (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  (x * 0x2545F4914F6CDD1D, ⟨x⟩)

/-- Constants hoisted to module level so they compile to cached cells rather
than a `Float.ofScientific` call per draw; see the note in `Tensor.lean`. -/
def twoPow53 : Float := 9007199254740992.0
def tiny : Float := 1e-12
def negTwo : Float := -2.0
def twoPi : Float := 6.283185307179586

/-- Uniform in `[0, 1)`, built from the top 53 bits so every float in the range
is reachable and the low-order bias of the shift register is discarded. -/
@[inline] def uniform (r : Rng) : Float × Rng :=
  let (u, r) := r.nextU64
  ((u >>> 11).toNat.toFloat / twoPow53, r)

/-- Uniform integer in `[0, n)`. Uses the modulo directly; the bias is around
`n / 2^64` and irrelevant at the sizes used here. -/
@[inline] def uniformNat (r : Rng) (n : Nat) : Nat × Rng :=
  let (u, r) := r.nextU64
  (if n == 0 then 0 else u.toNat % n, r)

/-- Standard normal via Box-Muller. Both generated values could be kept, but
weight init calls this once per scalar and the second value is simply dropped;
the cost is one `log`/`sqrt` pair per weight, paid once at startup. -/
def normal (r : Rng) : Float × Rng :=
  let (u1, r) := r.uniform
  let (u2, r) := r.uniform
  -- guard against log 0
  let u1 := if u1 < tiny then tiny else u1
  let mag := Float.sqrt (negTwo * Float.log u1)
  (mag * Float.cos (twoPi * u2), r)

/-- Normal scaled to a given standard deviation. -/
@[inline] def normalScaled (r : Rng) (sd : Float) : Float × Rng :=
  let (z, r) := r.normal
  (z * sd, r)

end Rng
end TinyLM
