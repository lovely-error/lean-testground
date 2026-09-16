import LeanTestground.NN.Model
/-!
# Forward and backward passes

There is no autodiff here. Every gradient below is derived by hand and written
out explicitly, which is the bulk of this file. The forward pass caches whatever
the backward pass needs (`LayerCache`), and the two are kept adjacent so a
change to one is hard to make without seeing the other.

`Train.gradCheck` compares the whole thing against central finite differences;
if you touch anything in this file, run it.

## Derivations used below

**RMSNorm.** With `r = (mean(x^2) + eps)^(-1/2)`, `y = x * r` and `out = y * g`:

    dg_j  = sum_t dout_tj * y_tj
    dy_j  = dout_j * g_j
    dx_j  = r * ( dy_j - (y_j / D) * sum_k dy_k * y_k )

The `sum_k dy_k y_k` term is the coupling through `r`: every input coordinate
moves the normalizer, so it feeds back into every output coordinate.

**Softmax.** For `p = softmax(s)`, `ds_i = p_i * (dp_i - sum_j p_j * dp_j)`.

**Attention**, per head, for query `t` over keys `u <= t`:

    dp_u    = sum_j dC_tj * V_uj
    dV_uj  += p_tu * dC_tj
    ds_u    = p_tu * (dp_u - sum_w p_tw dp_w)
    dQ_tj  += scale * sum_u ds_u * K_uj
    dK_uj  += scale * ds_u * Q_tj

**GELU** (tanh approximation), with `u = c(x + a x^3)`:

    d/dx = 0.5*(1 + tanh u) + 0.5*x*(1 - tanh(u)^2)*c*(1 + 3a x^2)
-/

namespace TinyLM

/-! ## Numeric constants

Bound once at module level. Referencing a `def` costs a call to a cached cell;
writing the literal inline would re-run `Float.ofScientific` every iteration (see
`Tensor.lean`). -/

def rmsEps : Float := 1e-5
def geluC : Float := 0.7978845608028654   -- sqrt(2/pi)
def geluA : Float := 0.044715

/-! `gelu` is `@[inline]` and runs once per feed-forward activation, so it is
the single most literal-sensitive function in the codebase. Writing `let half :=
0.5` inside its body put a `Float.ofScientific` call in the caller's inner loop
and cost **212ms** per `geluMat` on a 128x512 activation; with the constants
coming from top-level `def`s (`fHalf`, `f1`, `f3` in `Tensor.lean`) the same
call takes about 1ms. -/

@[inline] def gelu (x : Float) : Float :=
  let u := geluC * (x + geluA * x * x * x)
  fHalf * x * (f1 + u.tanh)

@[inline] def geluGrad (x : Float) : Float :=
  let u := geluC * (x + geluA * x * x * x)
  let th := u.tanh
  fHalf * (f1 + th)
    + fHalf * x * (f1 - th * th) * geluC * (f1 + f3 * geluA * x * x)

/-- What the backward pass needs from one block.

Only what is actually read: the residual inputs are absent because RMSNorm's
backward pass is expressed in terms of the normalized `y` and the inverse RMS
`r`, never the raw input. Caching them anyway would cost about 1.5 MB per
sequence for nothing. -/
structure LayerCache where
  r1   : Vec          -- 1/rms per row, first norm            (T)
  y1   : Mat          -- normalized, pre-gain                 (T x D)
  xn1  : Mat          -- normalized, post-gain                (T x D)
  q    : Mat
  k    : Mat
  v    : Mat
  probs : FloatArray  -- attention weights, h*T*T + t*T + u
  ctxo : Mat          -- attention output, pre-`wo`           (T x D)
  r2   : Vec
  y2   : Mat
  xn2  : Mat
  hpre : Mat          -- feed-forward pre-activation          (T x F)
  hact : Mat          -- feed-forward post-GELU               (T x F)
  deriving Inhabited

structure Cache where
  ids    : Array Nat
  seqLen : Nat
  layers : Array LayerCache
  rF     : Vec
  yF     : Mat
  xF     : Mat        -- final normalized activations         (T x D)
  deriving Inhabited

/-! ## RMSNorm -/

/-- Returns `(r, y, out)` where `r` is the per-row inverse RMS, `y = x * r`, and
`out = y * g`. -/
def rmsNormFwd (x : Mat) (g : Vec) : Vec × Mat × Mat := Id.run do
  let t := x.rows
  let d := x.cols
  let zero := f0
  let one := f1
  let dF := d.toFloat
  let eps := rmsEps
  let mut r := Vec.zeros t
  let mut y := Vec.zeros (t * d)
  let mut o := Vec.zeros (t * d)
  for i in [0:t] do
    let base := i * d
    let mut ss := zero
    for j in [0:d] do
      let xv := x.data.get! (base + j)
      ss := ss + xv * xv
    let ri := one / Float.sqrt (ss / dF + eps)
    r := r.set! i ri
    for j in [0:d] do
      let yv := x.data.get! (base + j) * ri
      y := y.set! (base + j) yv
      o := o.set! (base + j) (yv * g.get! j)
  return (r, ⟨t, d, y⟩, ⟨t, d, o⟩)

/-- Backward through RMSNorm. Adds the input gradient into `dx` and the gain
gradient into `dg`, returning both. -/
def rmsNormBwd (dOut : Mat) (y : Mat) (r : Vec) (g : Vec) (dx : Mat) (dg : Vec)
    : Mat × Vec := Id.run do
  let t := dOut.rows
  let d := dOut.cols
  let zero := f0
  let dF := d.toFloat
  let mut dxd := dx.data
  let mut dg := dg
  for i in [0:t] do
    let base := i * d
    let ri := r.get! i
    -- sum_k dy_k * y_k, the coupling through the normalizer
    let mut dot := zero
    for j in [0:d] do
      let dOutV := dOut.data.get! (base + j)
      let yv := y.data.get! (base + j)
      dg := dg.addAt j (dOutV * yv)
      dot := dot + (dOutV * g.get! j) * yv
    let dotScaled := dot / dF
    for j in [0:d] do
      let dyv := dOut.data.get! (base + j) * g.get! j
      let yv := y.data.get! (base + j)
      dxd := dxd.set! (base + j) (dxd.get! (base + j) + ri * (dyv - yv * dotScaled))
  return (⟨t, d, dxd⟩, dg)

/-! ## Attention

Scores are masked causally by construction: the inner loop simply stops at `u =
t` rather than materialising a mask and adding `-inf`. -/

/-- Causal multi-head attention. Returns `(probs, ctxOut)`. -/
def attentionFwd (cfg : Config) (q k v : Mat) : FloatArray × Mat := Id.run do
  let t := q.rows
  let d := cfg.dModel
  let h := cfg.nHeads
  let dh := cfg.dHead
  let zero := f0
  let one := f1
  let scale := one / Float.sqrt dh.toFloat
  let neg := fNegBig
  let mut probs := Vec.zeros (h * t * t)
  let mut out := Vec.zeros (t * d)
  let mut scratch := Vec.zeros t
  for hi in [0:h] do
    let base := hi * dh
    let pBase := hi * t * t
    for ti in [0:t] do
      let qBase := ti * d + base
      -- scores over the allowed keys, tracking the max for a stable softmax
      let mut mx := neg
      for u in [0:ti+1] do
        let kBase := u * d + base
        let mut dot := zero
        for j in [0:dh] do
          dot := dot + q.data.get! (qBase + j) * k.data.get! (kBase + j)
        let sc := dot * scale
        scratch := scratch.set! u sc
        if sc > mx then mx := sc
      let mut denom := zero
      for u in [0:ti+1] do
        let e := Float.exp (scratch.get! u - mx)
        scratch := scratch.set! u e
        denom := denom + e
      let inv := one / denom
      let pRow := pBase + ti * t
      for u in [0:ti+1] do
        probs := probs.set! (pRow + u) (scratch.get! u * inv)
      -- weighted sum of values
      let oBase := ti * d + base
      for u in [0:ti+1] do
        let pw := probs.get! (pRow + u)
        let vBase := u * d + base
        for j in [0:dh] do
          out := out.set! (oBase + j) (out.get! (oBase + j) + pw * v.data.get! (vBase + j))
  return (probs, ⟨t, d, out⟩)

/-- Backward through causal attention. Returns `(dq, dk, dv)`. -/
def attentionBwd (cfg : Config) (q k v : Mat) (probs : FloatArray) (dCtx : Mat)
    : Mat × Mat × Mat := Id.run do
  let t := q.rows
  let d := cfg.dModel
  let h := cfg.nHeads
  let dh := cfg.dHead
  let zero := f0
  let one := f1
  let scale := one / Float.sqrt dh.toFloat
  let mut dq := Vec.zeros (t * d)
  let mut dk := Vec.zeros (t * d)
  let mut dv := Vec.zeros (t * d)
  let mut dp := Vec.zeros t
  for hi in [0:h] do
    let base := hi * dh
    let pBase := hi * t * t
    for ti in [0:t] do
      let pRow := pBase + ti * t
      let cBase := ti * d + base
      -- dp_u = sum_j dC_tj V_uj, and dV picks up p_tu * dC_tj on the way
      let mut wsum := zero
      for u in [0:ti+1] do
        let vBase := u * d + base
        let pw := probs.get! (pRow + u)
        let mut acc := f0
        for j in [0:dh] do
          let dc := dCtx.data.get! (cBase + j)
          acc := acc + dc * v.data.get! (vBase + j)
          dv := dv.set! (vBase + j) (dv.get! (vBase + j) + pw * dc)
        dp := dp.set! u acc
        wsum := wsum + pw * acc
      -- softmax backward, then scatter into dq/dk
      let qBase := ti * d + base
      for u in [0:ti+1] do
        let pw := probs.get! (pRow + u)
        let ds := pw * (dp.get! u - wsum) * scale
        let kBase := u * d + base
        for j in [0:dh] do
          dq := dq.set! (qBase + j) (dq.get! (qBase + j) + ds * k.data.get! (kBase + j))
          dk := dk.set! (kBase + j) (dk.get! (kBase + j) + ds * q.data.get! (qBase + j))
  return (⟨t, d, dq⟩, ⟨t, d, dk⟩, ⟨t, d, dv⟩)

/-! ## Forward -/

/-- Embed token ids and add positions. -/
def embed (p : Params) (ids : Array Nat) : Mat := Id.run do
  let d := p.cfg.dModel
  let t := ids.size
  let mut x := Vec.zeros (t * d)
  for i in [0:t] do
    let tok := ids[i]!
    let tBase := tok * d
    let pBase := i * d
    let base := i * d
    for j in [0:d] do
      x := x.set! (base + j)
        (p.tokEmb.data.get! (tBase + j) + p.posEmb.data.get! (pBase + j))
  return ⟨t, d, x⟩

/-- Apply GELU elementwise, returning a fresh matrix. -/
private def geluMat (m : Mat) : Mat := Id.run do
  let n := m.size
  let mut o := Vec.zeros n
  for i in [0:n] do
    o := o.set! i (gelu (m.data.get! i))
  return { m with data := o }

/-- Run the network and keep everything the backward pass will need. Produces
the final normalized activations; turning those into logits is a separate step
so that sampling can project only the last row. -/
def forward (p : Params) (ids : Array Nat) : Cache := Id.run do
  let cfg := p.cfg
  let mut x := embed p ids
  let mut caches : Array LayerCache := #[]
  for l in p.layers do
    let xIn := x
    let (r1, y1, xn1) := rmsNormFwd xIn l.ln1g
    -- `xIn` and `xMid` below feed the residual adds only; neither is cached,
    -- because nothing in the backward pass reads them.
    let q := xn1.mul l.wq
    let k := xn1.mul l.wk
    let v := xn1.mul l.wv
    let (probs, ctxo) := attentionFwd cfg q k v
    let attnOut := ctxo.mul l.wo
    let xMid := (Mat.zeros xIn.rows xIn.cols).addInto xIn |>.addInto attnOut
    let (r2, y2, xn2) := rmsNormFwd xMid l.ln2g
    let hpre := (xn2.mul l.w1).addRowVec l.b1
    let hact := geluMat hpre
    let mlpOut := (hact.mul l.w2).addRowVec l.b2
    x := (Mat.zeros xMid.rows xMid.cols).addInto xMid |>.addInto mlpOut
    caches := caches.push
      { r1, y1, xn1, q, k, v, probs, ctxo, r2, y2, xn2, hpre, hact }
  let (rF, yF, xF) := rmsNormFwd x p.lnFg
  return { ids, seqLen := ids.size, layers := caches, rF, yF, xF }

/-- Logits for every position: `xF @ head + headB`. -/
def logitsAll (p : Params) (c : Cache) : Mat :=
  (c.xF.mul p.head).addRowVec p.headB

/-- Logits for the final position only. Generation needs one row, and computing
all `T` of them would multiply the cost of every sampled token by the context
length. -/
def logitsLast (p : Params) (c : Cache) : Vec := Id.run do
  let d := p.cfg.dModel
  let vsz := p.cfg.vocab
  let zero := f0
  let base := (c.seqLen - 1) * d
  let mut o := Vec.zeros vsz
  for j in [0:vsz] do
    o := o.set! j (p.headB.get! j)
  for i in [0:d] do
    let xv := c.xF.data.get! (base + i)
    if xv != zero then
      let hBase := i * vsz
      for j in [0:vsz] do
        o := o.set! j (o.get! j + xv * p.head.data.get! (hBase + j))
  return o

/-! ## Loss

Mean cross-entropy over the sequence. `targets[i]` is the token that should
follow `ids[i]`; positions whose target is `none` (padding) are skipped and
excluded from the mean. -/

/-- Returns `(loss, dLogits)` with `dLogits` already averaged over scored
positions, so the caller never has to remember to divide. -/
def crossEntropy (logits : Mat) (targets : Array (Option Nat)) : Float × Mat := Id.run do
  let t := logits.rows
  let vsz := logits.cols
  let zero := f0
  let one := f1
  let neg := fNegBig
  let mut dl := Vec.zeros (t * vsz)
  let mut total := zero
  let mut counted := 0
  for i in [0:t] do
    match targets[i]! with
    | none => pure ()
    | some tgt =>
      let base := i * vsz
      let mut mx := neg
      for j in [0:vsz] do
        let z := logits.data.get! (base + j)
        if z > mx then mx := z
      let mut denom := zero
      for j in [0:vsz] do
        denom := denom + Float.exp (logits.data.get! (base + j) - mx)
      let logDenom := Float.log denom
      total := total + (logDenom + mx - logits.data.get! (base + tgt))
      counted := counted + 1
      let inv := one / denom
      for j in [0:vsz] do
        dl := dl.set! (base + j) (Float.exp (logits.data.get! (base + j) - mx) * inv)
      dl := dl.set! (base + tgt) (dl.get! (base + tgt) - one)
  -- average over scored positions
  if counted > 0 then
    let scale := one / counted.toFloat
    for i in [0:t * vsz] do
      dl := dl.set! i (dl.get! i * scale)
    total := total * scale
  return (total, ⟨t, vsz, dl⟩)

/-! ## Backward

Accumulates into `g`, which is a `Params` of the same shape, so a mini-batch can
be summed by calling this repeatedly with the same buffer. -/

def backward (p : Params) (c : Cache) (dLogits : Mat) (g : Params) : Params := Id.run do
  let cfg := p.cfg
  let d := cfg.dModel
  let t := c.seqLen
  let mut g := g

  -- Output head
  let dxF := dLogits.mulTB p.head
  g := { g with head := g.head.mulTAInto c.xF dLogits
                headB := Mat.sumRowsInto g.headB dLogits }

  -- Final RMSNorm
  let (dxAcc, lnFg') := rmsNormBwd dxF c.yF c.rF p.lnFg (Mat.zeros t d) g.lnFg
  g := { g with lnFg := lnFg' }
  let mut dx := dxAcc

  -- Blocks, last to first
  let mut li := cfg.nLayers
  while li > 0 do
    li := li - 1
    let l := p.layers[li]!
    let lc := c.layers[li]!
    let mut gl := g.layers[li]!

    -- residual: the block output feeds both the MLP branch and the skip
    let dMlp := dx
    let mut dxMid := dx

    -- feed-forward, second matmul
    let dHact := dMlp.mulTB l.w2
    gl := { gl with w2 := gl.w2.mulTAInto lc.hact dMlp
                    b2 := Mat.sumRowsInto gl.b2 dMlp }
    -- GELU
    let mut dHpre := Vec.zeros (t * cfg.dFF)
    for i in [0:t * cfg.dFF] do
      dHpre := dHpre.set! i (dHact.data.get! i * geluGrad (lc.hpre.data.get! i))
    let dHpreM : Mat := ⟨t, cfg.dFF, dHpre⟩
    -- feed-forward, first matmul
    let dxn2 := dHpreM.mulTB l.w1
    gl := { gl with w1 := gl.w1.mulTAInto lc.xn2 dHpreM
                    b1 := Mat.sumRowsInto gl.b1 dHpreM }
    -- second norm
    let (dxMid', ln2g') := rmsNormBwd dxn2 lc.y2 lc.r2 l.ln2g dxMid gl.ln2g
    dxMid := dxMid'
    gl := { gl with ln2g := ln2g' }

    -- residual: xMid feeds both the attention branch and the skip
    let dAttn := dxMid
    let mut dxIn := dxMid

    -- attention output projection
    let dCtx := dAttn.mulTB l.wo
    gl := { gl with wo := gl.wo.mulTAInto lc.ctxo dAttn }
    -- attention proper
    let (dq, dk, dv) := attentionBwd cfg lc.q lc.k lc.v lc.probs dCtx
    -- q/k/v projections all read the same normalized input, so their input
    -- gradients sum
    let mut dxn1 := dq.mulTB l.wq
    dxn1 := dxn1.addInto (dk.mulTB l.wk)
    dxn1 := dxn1.addInto (dv.mulTB l.wv)
    gl := { gl with wq := gl.wq.mulTAInto lc.xn1 dq
                    wk := gl.wk.mulTAInto lc.xn1 dk
                    wv := gl.wv.mulTAInto lc.xn1 dv }
    -- first norm
    let (dxIn', ln1g') := rmsNormBwd dxn1 lc.y1 lc.r1 l.ln1g dxIn gl.ln1g
    dxIn := dxIn'
    gl := { gl with ln1g := ln1g' }

    g := { g with layers := g.layers.set! li gl }
    dx := dxIn

  -- Embeddings
  let mut gTok := g.tokEmb.data
  let mut gPos := g.posEmb.data
  for i in [0:t] do
    let tok := c.ids[i]!
    let tBase := tok * d
    let base := i * d
    for j in [0:d] do
      let gv := dx.data.get! (base + j)
      gTok := gTok.set! (tBase + j) (gTok.get! (tBase + j) + gv)
      gPos := gPos.set! (base + j) (gPos.get! (base + j) + gv)
  g := { g with tokEmb := { g.tokEmb with data := gTok }
                posEmb := { g.posEmb with data := gPos } }
  return g

/-- Forward, loss and backward for one sequence, accumulating into `g`. -/
def forwardBackward (p : Params) (ids : Array Nat) (targets : Array (Option Nat))
    (g : Params) : Float × Params :=
  let c := forward p ids
  let logits := logitsAll p c
  let (loss, dLogits) := crossEntropy logits targets
  (loss, backward p c dLogits g)

end TinyLM
