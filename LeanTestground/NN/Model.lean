import LeanTestground.NN.Tensor
import LeanTestground.NN.Rng
/-!
# Model definition: a decoder-only transformer

The architecture is the standard GPT recipe, reduced until it fits a CPU budget:
learned token + position embeddings, then `nLayers` pre-norm blocks of causal
multi-head self-attention and a GELU feed-forward, then a final norm and an
untied output projection.

Three deviations from GPT-2 proper, all chosen to keep the hand-written backward
pass short and its derivation checkable:

* **RMSNorm instead of LayerNorm.** No mean subtraction, so the backward pass is
  one dot product per row instead of two, and there is no bias to carry.
* **Untied output head.** Tying it to the embedding would save `vocab * dModel`
  parameters, but it would *not* save any FLOPs (the projection still runs), and
  it routes two different gradients into one buffer. Untied is the version whose
  gradient is obviously correct.
* **Biases only in the feed-forward.** Attention projections and the norms carry
  no bias; they contribute almost nothing at this scale.

## Parameter layout

Everything is reachable as a flat `Array FloatArray` in a fixed canonical order
(`tensors` / `ofTensors`). The optimizer and the checkpoint writer both work on
that flat view, so neither has to know the block structure -- and adding a
parameter means touching the layout in exactly one place.
-/

namespace TinyLM

structure Config where
  vocab   : Nat
  dModel  : Nat
  nHeads  : Nat
  nLayers : Nat
  dFF     : Nat
  ctx     : Nat
  deriving Inhabited, Repr, BEq

namespace Config

/-- Width of a single attention head. -/
@[inline] def dHead (c : Config) : Nat := c.dModel / c.nHeads

/-- The default is sized so that a full training run finishes on a 6-core CPU in
roughly an hour, while staying near the compute-optimal token/parameter ratio
for the ~1M-token corpus slice. -/
def default : Config :=
  { vocab := 2048, dModel := 128, nHeads := 4, nLayers := 4, dFF := 512, ctx := 128 }

/-- A quarter-size model, for smoke tests and gradient checks. -/
def tiny : Config :=
  { vocab := 256, dModel := 32, nHeads := 2, nLayers := 2, dFF := 64, ctx := 16 }

def numParams (c : Config) : Nat :=
  c.vocab * c.dModel                    -- token embedding
  + c.ctx * c.dModel                    -- position embedding
  + c.nLayers * ( c.dModel              -- ln1 gain
                + 4 * c.dModel * c.dModel  -- wq, wk, wv, wo
                + c.dModel              -- ln2 gain
                + c.dModel * c.dFF + c.dFF   -- w1, b1
                + c.dFF * c.dModel + c.dModel) -- w2, b2
  + c.dModel                            -- final norm gain
  + c.dModel * c.vocab + c.vocab        -- output head

def toString (c : Config) : String :=
  s!"vocab={c.vocab} dModel={c.dModel} heads={c.nHeads} layers={c.nLayers} " ++
  s!"dFF={c.dFF} ctx={c.ctx} params={c.numParams}"

end Config

/-- One transformer block's parameters. Weight matrices are stored
input-major (`in x out`) so the forward pass is a plain `x @ W`. -/
structure Layer where
  ln1g : Vec   -- RMSNorm gain before attention        (dModel)
  wq   : Mat   -- query projection                     (dModel x dModel)
  wk   : Mat   -- key projection                       (dModel x dModel)
  wv   : Mat   -- value projection                     (dModel x dModel)
  wo   : Mat   -- output projection                    (dModel x dModel)
  ln2g : Vec   -- RMSNorm gain before the feed-forward (dModel)
  w1   : Mat   -- feed-forward in                      (dModel x dFF)
  b1   : Vec   --                                      (dFF)
  w2   : Mat   -- feed-forward out                     (dFF x dModel)
  b2   : Vec   --                                      (dModel)
  deriving Inhabited

structure Params where
  cfg    : Config
  tokEmb : Mat   -- (vocab x dModel)
  posEmb : Mat   -- (ctx x dModel)
  layers : Array Layer
  lnFg   : Vec   -- (dModel)
  head   : Mat   -- (dModel x vocab)
  headB  : Vec   -- (vocab)
  deriving Inhabited

namespace Params

/-- All parameter buffers in canonical order. The optimizer, the gradient
accumulator and the checkpoint format all agree to use this order and nothing
else, so it is the single point of truth for the layout. -/
def tensors (p : Params) : Array FloatArray := Id.run do
  let mut out : Array FloatArray := #[p.tokEmb.data, p.posEmb.data]
  for l in p.layers do
    out := out ++ #[l.ln1g, l.wq.data, l.wk.data, l.wv.data, l.wo.data,
                    l.ln2g, l.w1.data, l.b1, l.w2.data, l.b2]
  return out ++ #[p.lnFg, p.head.data, p.headB]

/-- Rebuild from buffers in `tensors` order. Shapes come from the config, so the
flat view carries no shape information of its own. -/
def ofTensors (cfg : Config) (ts : Array FloatArray) : Params := Id.run do
  let d := cfg.dModel
  let f := cfg.dFF
  let mut layers : Array Layer := #[]
  for l in [0:cfg.nLayers] do
    let b := 2 + l * 10
    layers := layers.push
      { ln1g := ts[b]!
        wq := ⟨d, d, ts[b+1]!⟩, wk := ⟨d, d, ts[b+2]!⟩
        wv := ⟨d, d, ts[b+3]!⟩, wo := ⟨d, d, ts[b+4]!⟩
        ln2g := ts[b+5]!
        w1 := ⟨d, f, ts[b+6]!⟩, b1 := ts[b+7]!
        w2 := ⟨f, d, ts[b+8]!⟩, b2 := ts[b+9]! }
  let tail := 2 + cfg.nLayers * 10
  return { cfg
           tokEmb := ⟨cfg.vocab, d, ts[0]!⟩
           posEmb := ⟨cfg.ctx, d, ts[1]!⟩
           layers
           lnFg := ts[tail]!
           head := ⟨d, cfg.vocab, ts[tail+1]!⟩
           headB := ts[tail+2]! }

/-- A zero-filled parameter set of the same shape; this is what a gradient is. -/
def zeros (cfg : Config) : Params :=
  let d := cfg.dModel
  let f := cfg.dFF
  { cfg
    tokEmb := Mat.zeros cfg.vocab d
    posEmb := Mat.zeros cfg.ctx d
    layers := (Array.range cfg.nLayers).map fun _ =>
      { ln1g := Vec.zeros d
        wq := Mat.zeros d d, wk := Mat.zeros d d
        wv := Mat.zeros d d, wo := Mat.zeros d d
        ln2g := Vec.zeros d
        w1 := Mat.zeros d f, b1 := Vec.zeros f
        w2 := Mat.zeros f d, b2 := Vec.zeros d }
    lnFg := Vec.zeros d
    head := Mat.zeros d cfg.vocab
    headB := Vec.zeros cfg.vocab }

/-! ## Initialisation

Normal draws scaled by fan-in, with the two residual-output projections (`wo`
and `w2`) additionally divided by `sqrt(2 * nLayers)`. That second factor is the
GPT-2 trick: without it the residual stream's variance grows with depth, and a
model this narrow starts out saturated. -/

private def randBuf (n : Nat) (sd : Float) (r : Rng) : FloatArray × Rng := Id.run do
  let mut a := FloatArray.emptyWithCapacity n
  let mut r := r
  for _ in [0:n] do
    let (z, r') := r.normalScaled sd
    a := a.push z
    r := r'
  return (a, r)

private def randMat (rows cols : Nat) (sd : Float) (r : Rng) : Mat × Rng :=
  let (a, r) := randBuf (rows * cols) sd r
  (⟨rows, cols, a⟩, r)

def init (cfg : Config) (r : Rng) : Params := Id.run do
  let d := cfg.dModel
  let f := cfg.dFF
  let one := f1
  let sdEmb := 0.02
  let sdIn := one / Float.sqrt d.toFloat
  let sdFF := one / Float.sqrt f.toFloat
  let depthScale := one / Float.sqrt (2.0 * cfg.nLayers.toFloat)
  let mut r := r
  let (tokEmb, r') := randMat cfg.vocab d sdEmb r; r := r'
  let (posEmb, r') := randMat cfg.ctx d sdEmb r; r := r'
  let mut layers : Array Layer := #[]
  for _ in [0:cfg.nLayers] do
    let (wq, r') := randMat d d sdIn r; r := r'
    let (wk, r') := randMat d d sdIn r; r := r'
    let (wv, r') := randMat d d sdIn r; r := r'
    let (wo, r') := randMat d d (sdIn * depthScale) r; r := r'
    let (w1, r') := randMat d f sdIn r; r := r'
    let (w2, r') := randMat f d (sdFF * depthScale) r; r := r'
    layers := layers.push
      { ln1g := Vec.const d one, wq, wk, wv, wo
        ln2g := Vec.const d one
        w1, b1 := Vec.zeros f
        w2, b2 := Vec.zeros d }
  let (head, _) := randMat d cfg.vocab sdIn r
  return { cfg, tokEmb, posEmb, layers
           lnFg := Vec.const d one
           head, headB := Vec.zeros cfg.vocab }

/-! ## Checkpoint format

`TINYLM01`, six little-endian `UInt64` config fields, then every parameter as a
little-endian IEEE-754 double in `tensors` order. Doubles rather than floats
because that is what `FloatArray` holds; halving the file would mean a
conversion on both ends for no benefit while training on CPU. -/

private def magic : String := "TINYLM01"

private def pushU64 (b : ByteArray) (x : UInt64) : ByteArray := Id.run do
  let mut b := b
  for i in [0:8] do
    b := b.push (((x >>> (8 * i.toUInt64)) &&& 0xFF).toUInt8)
  return b

private def readU64 (b : ByteArray) (off : Nat) : UInt64 := Id.run do
  let mut x : UInt64 := 0
  for i in [0:8] do
    x := x ||| (b.get! (off + i)).toUInt64 <<< (8 * i.toUInt64)
  return x

def serialize (p : Params) : ByteArray := Id.run do
  let c := p.cfg
  let mut b := ByteArray.emptyWithCapacity (64 + 8 * c.numParams)
  for ch in magic.toList do
    b := b.push ch.toUInt8
  for x in [c.vocab, c.dModel, c.nHeads, c.nLayers, c.dFF, c.ctx] do
    b := pushU64 b x.toUInt64
  for t in p.tensors do
    for i in [0:t.size] do
      b := pushU64 b (t.get! i).toBits
  return b

def deserialize (b : ByteArray) : Except String Params := Id.run do
  if b.size < 56 then
    return .error "checkpoint too short"
  let hdr := String.ofList ((List.range 8).map (fun i => Char.ofNat (b.get! i).toNat))
  if hdr != magic then
    return .error s!"bad magic: expected {magic}, got {hdr}"
  let fields := (List.range 6).map (fun i => (readU64 b (8 + 8 * i)).toNat)
  let cfg : Config := match fields with
    | [v, d, h, l, f, t] =>
      { vocab := v, dModel := d, nHeads := h, nLayers := l, dFF := f, ctx := t }
    | _ => Config.default
  let expected := 56 + 8 * cfg.numParams
  if b.size != expected then
    return .error s!"size mismatch: header implies {expected} bytes, file has {b.size}"
  -- Walk `tensors` order using a zero model purely as a shape template.
  let template := (Params.zeros cfg).tensors
  let mut ts : Array FloatArray := #[]
  let mut off := 56
  for t in template do
    let n := t.size
    let mut a := FloatArray.emptyWithCapacity n
    for i in [0:n] do
      a := a.push (Float.ofBits (readU64 b (off + 8 * i)))
    ts := ts.push a
    off := off + 8 * n
  return .ok (ofTensors cfg ts)

end Params
end TinyLM
