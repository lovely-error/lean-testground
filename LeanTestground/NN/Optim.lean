import LeanTestground.NN.Model
/-!
# AdamW, gradient clipping, and the learning-rate schedule

Adam rather than plain SGD is not optional at this scale. The parameter groups
here have wildly different gradient magnitudes -- embedding rows for rare words
receive a gradient only on the steps where that word appears, while the norm
gains receive one every step -- and a single global step size cannot serve both.
Adam's per-coordinate normalisation is what lets one learning rate cover them.

Weight decay is decoupled (the "W" in AdamW): applied directly to the parameter
rather than folded into the gradient, so it does not get divided by Adam's
second-moment estimate.
-/

namespace TinyLM

/-- Which parameters weight decay applies to, in `Params.tensors` order.

Decaying a norm gain pulls it toward zero, which scales the whole activation
stream down; decaying a bias just adds a systematic offset. Neither is what
weight decay is for, so both are excluded -- only the matrices are decayed. -/
def decayMask (cfg : Config) : Array Bool := Id.run do
  let mut m : Array Bool := #[true, true]        -- tokEmb, posEmb
  for _ in [0:cfg.nLayers] do
    m := m ++ #[false,                            -- ln1g
                true, true, true, true,           -- wq, wk, wv, wo
                false,                            -- ln2g
                true, false,                      -- w1, b1
                true, false]                      -- w2, b2
  return m ++ #[false, true, false]               -- lnFg, head, headB

structure AdamState where
  m    : Array FloatArray   -- first moment,  `tensors` order
  v    : Array FloatArray   -- second moment, `tensors` order
  step : Nat
  deriving Inhabited

namespace AdamState

def init (cfg : Config) : AdamState :=
  let shapes := (Params.zeros cfg).tensors
  { m := shapes.map (fun t => Vec.zeros t.size)
    v := shapes.map (fun t => Vec.zeros t.size)
    step := 0 }

end AdamState

structure AdamConfig where
  lr      : Float := 3e-4
  beta1   : Float := 0.9
  beta2   : Float := 0.95   -- 0.95 rather than 0.999: short runs, and the
                            -- second moment needs to track a fast-moving loss
  eps     : Float := 1e-8
  weightDecay : Float := 0.1
  clipNorm : Float := 1.0
  deriving Inhabited

/-- Global L2 norm of a gradient, over every parameter at once. -/
def gradNorm (g : Params) : Float := Id.run do
  let mut acc := f0
  for t in g.tensors do
    for i in [0:t.size] do
      let x := t.get! i
      acc := acc + x * x
  return Float.sqrt acc

/-! ## The step

One fused pass over every parameter: clip scaling, both moment updates, bias
correction and the decoupled decay all happen in the same loop, so the
parameter array is walked once rather than five times. -/

def adamStep (p : Params) (g : Params) (st : AdamState) (ac : AdamConfig) (lr : Float)
    : Params × AdamState × Float :=
  Id.run do
    let cfg := p.cfg
    let one := f1
    let zero := f0
    let gn := gradNorm g
    -- Clip by global norm: rescale everything by the same factor so the
    -- gradient's direction is preserved and only its length is capped.
    let clipScale := if gn > ac.clipNorm && gn > zero then ac.clipNorm / gn else one
    let step := st.step + 1
    let bc1 := one - Float.pow ac.beta1 step.toFloat
    let bc2 := one - Float.pow ac.beta2 step.toFloat
    let mask := decayMask cfg
    let ps := p.tensors
    let gs := g.tensors
    let mut newPs : Array FloatArray := #[]
    let mut newM : Array FloatArray := #[]
    let mut newV : Array FloatArray := #[]
    for idx in [0:ps.size] do
      let mut pt := ps[idx]!
      let gt := gs[idx]!
      let mut mt := st.m[idx]!
      let mut vt := st.v[idx]!
      let decay := if mask[idx]! then ac.weightDecay * lr else zero
      let n := pt.size
      for i in [0:n] do
        let gv := gt.get! i * clipScale
        let mv := ac.beta1 * mt.get! i + (one - ac.beta1) * gv
        let vv := ac.beta2 * vt.get! i + (one - ac.beta2) * gv * gv
        mt := mt.set! i mv
        vt := vt.set! i vv
        let mHat := mv / bc1
        let vHat := vv / bc2
        let pv := pt.get! i
        pt := pt.set! i (pv - lr * (mHat / (Float.sqrt vHat + ac.eps)) - decay * pv)
      newPs := newPs.push pt
      newM := newM.push mt
      newV := newV.push vt
    return (Params.ofTensors cfg newPs, { m := newM, v := newV, step }, gn)

/-! ## Schedule

Linear warmup then cosine decay to a floor of `lr/10`. The warmup matters more
than usual here: Adam's second-moment estimate is meaningless for the first
handful of steps, and a full-size step taken against it early on can push the
norm gains somewhere the run never recovers from. -/

def lrAt (base : Float) (step warmup total : Nat) : Float :=
  let one := f1
  let half := fHalf
  let tenth := fTenth
  if step < warmup then
    base * (step.toFloat + one) / warmup.toFloat
  else
    let progress :=
      if total > warmup then
        (step - warmup).toFloat / (total - warmup).toFloat
      else one
    let progress := if progress > one then one else progress
    let cos := half * (one + Float.cos (3.141592653589793 * progress))
    base * (tenth + (one - tenth) * cos)

end TinyLM
