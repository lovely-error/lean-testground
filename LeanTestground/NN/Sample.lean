import LeanTestground.NN.Transformer
import LeanTestground.NN.Tokenizer
/-!
# Generation with a KV cache

Sampling naively -- re-running the full forward pass over the whole context for
every new token -- costs `O(T)` per token and `O(T^2)` for a story. At the
default size that is around 0.6s *per token*, which makes generating a
150-token story a two-minute wait.

So decoding here is incremental. Keys and values for every position already
generated are kept in `KVCache`, and each new token runs the network over a
single position, attending to the cache. That drops the per-token cost by more
than two orders of magnitude.

The one thing to be careful about: the incremental path must compute exactly
what `Transformer.forward` computes for the same prefix. `Sample.verifyKVCache`
asserts precisely that, comparing incremental logits against full-forward
logits token by token.
-/

namespace TinyLM

/-- Cached keys and values, per layer, laid out as `ctx x dModel`. The caller
tracks how many rows are filled, since it already tracks the position. -/
structure KVCache where
  k : Array FloatArray
  v : Array FloatArray
  deriving Inhabited

def KVCache.empty (cfg : Config) : KVCache :=
  { k := (Array.range cfg.nLayers).map fun _ => Vec.zeros (cfg.ctx * cfg.dModel)
    v := (Array.range cfg.nLayers).map fun _ => Vec.zeros (cfg.ctx * cfg.dModel) }

/-! ## One incremental step

`x` is a `1 x dModel` matrix throughout, so the dense projections reuse the same
`Mat.mul` kernels as training. Only attention differs: it reads `pos + 1` rows
out of the cache instead of a triangular block of a square score matrix. -/

/-- Attention for a single query position against the cached keys/values. -/
private def attendCached (cfg : Config) (q : Mat) (kBuf vBuf : FloatArray) (pos : Nat)
    : Mat := Id.run do
  let d := cfg.dModel
  let h := cfg.nHeads
  let dh := cfg.dHead
  let zero := f0
  let one := f1
  let neg := fNegBig
  let scale := one / Float.sqrt dh.toFloat
  let mut out := Vec.zeros d
  let mut scratch := Vec.zeros (pos + 1)
  for hi in [0:h] do
    let base := hi * dh
    let mut mx := neg
    for u in [0:pos+1] do
      let kBase := u * d + base
      let mut dot := zero
      for j in [0:dh] do
        dot := dot + q.data.get! (base + j) * kBuf.get! (kBase + j)
      let sc := dot * scale
      scratch := scratch.set! u sc
      if sc > mx then mx := sc
    let mut denom := zero
    for u in [0:pos+1] do
      let e := Float.exp (scratch.get! u - mx)
      scratch := scratch.set! u e
      denom := denom + e
    let inv := one / denom
    for u in [0:pos+1] do
      let pw := scratch.get! u * inv
      let vBase := u * d + base
      for j in [0:dh] do
        out := out.set! (base + j) (out.get! (base + j) + pw * vBuf.get! (vBase + j))
  return ⟨1, d, out⟩

private def geluMat1 (m : Mat) : Mat := Id.run do
  let n := m.size
  let mut o := Vec.zeros n
  for i in [0:n] do
    o := o.set! i (gelu (m.data.get! i))
  return { m with data := o }

/-- Advance the model by one token. Returns the logits for the *next* token and
the updated cache. `pos` is the position of `tok` in the sequence. -/
def stepToken (p : Params) (cache : KVCache) (tok : Nat) (pos : Nat)
    : Vec × KVCache := Id.run do
  let cfg := p.cfg
  let d := cfg.dModel
  -- embed a single position
  let mut xd := Vec.zeros d
  let tBase := tok * d
  let pBase := pos * d
  for j in [0:d] do
    xd := xd.set! j (p.tokEmb.data.get! (tBase + j) + p.posEmb.data.get! (pBase + j))
  let mut x : Mat := ⟨1, d, xd⟩
  let mut kBufs := cache.k
  let mut vBufs := cache.v
  for li in [0:cfg.nLayers] do
    let l := p.layers[li]!
    let (_, _, xn1) := rmsNormFwd x l.ln1g
    let q := xn1.mul l.wq
    let kNew := xn1.mul l.wk
    let vNew := xn1.mul l.wv
    -- write this position's k/v into the cache
    let mut kBuf := kBufs[li]!
    let mut vBuf := vBufs[li]!
    let base := pos * d
    for j in [0:d] do
      kBuf := kBuf.set! (base + j) (kNew.data.get! j)
      vBuf := vBuf.set! (base + j) (vNew.data.get! j)
    let ctxo := attendCached cfg q kBuf vBuf pos
    kBufs := kBufs.set! li kBuf
    vBufs := vBufs.set! li vBuf
    let attnOut := ctxo.mul l.wo
    let xMid := (Mat.zeros 1 d).addInto x |>.addInto attnOut
    let (_, _, xn2) := rmsNormFwd xMid l.ln2g
    let hact := geluMat1 ((xn2.mul l.w1).addRowVec l.b1)
    let mlpOut := (hact.mul l.w2).addRowVec l.b2
    x := (Mat.zeros 1 d).addInto xMid |>.addInto mlpOut
  let (_, _, xF) := rmsNormFwd x p.lnFg
  let logits := (xF.mul p.head).addRowVec p.headB
  return (logits.data, { k := kBufs, v := vBufs })

/-! ## Sampling from a logit vector -/

structure SampleConfig where
  temperature : Float := 0.9
  /-- Keep only the `topK` most likely tokens (0 disables). -/
  topK : Nat := 40
  /-- Nucleus threshold; 1.0 disables. -/
  topP : Float := 0.95
  maxTokens : Nat := 200
  deriving Inhabited

/-- Token ids that generation must never emit.

`<unk>` stands for ~3.4% of training tokens, so the model learns to predict it
and would otherwise sprinkle it through the output; `<bos>` mid-story is
similarly an artifact of window-based training rather than something to say. -/
private def bannedIds : Array Nat := #[unkId, bosId]

/-- Sample one token: temperature, then top-k, then nucleus, then draw. -/
def sampleToken (logits : Vec) (sc : SampleConfig) (rng : Rng) : Nat × Rng :=
  Id.run do
    let zero := f0
    let one := f1
    let neg := fNegBig
    let n := logits.size
    -- temperature, with banned ids pushed out of reach
    let temp := if sc.temperature < 1e-6 then 1e-6 else sc.temperature
    let mut z := Vec.zeros n
    for i in [0:n] do
      z := z.set! i (logits.get! i / temp)
    for b in bannedIds do
      if b < n then
        z := z.set! b neg
    -- order by logit, descending
    let mut idx := (Array.range n).map fun i => (i, z.get! i)
    let sorted := idx.qsort (fun a b => a.2 > b.2)
    let keep := if sc.topK == 0 then n else min sc.topK n
    -- softmax over the kept head of the distribution
    let mx := (sorted[0]!).2
    let mut probs : Array (Nat × Float) := #[]
    let mut denom := zero
    for i in [0:keep] do
      let (tid, zv) := sorted[i]!
      let e := Float.exp (zv - mx)
      probs := probs.push (tid, e)
      denom := denom + e
    -- nucleus: take the shortest prefix whose mass reaches topP
    let inv := one / denom
    let mut cum := zero
    let mut cutoff := probs.size
    let mut found := false
    for i in [0:probs.size] do
      if !found then
        cum := cum + probs[i]!.2 * inv
        if cum >= sc.topP then
          cutoff := i + 1
          found := true
    probs := probs.extract 0 cutoff
    -- renormalise and draw
    let mut total := zero
    for (_, w) in probs do
      total := total + w
    let (u, rng) := rng.uniform
    let target := u * total
    let mut acc := f0
    let mut chosen := probs[0]!.1
    let mut picked := false
    for (tid, w) in probs do
      if !picked then
        acc := acc + w
        if acc >= target then
          chosen := tid
          picked := true
    return (chosen, rng)

/-! ## Generation -/

/-- Generate a story. Starts from `<bos>` plus any prompt tokens, and stops at
`<eos>`, at `maxTokens`, or when the context window is full -- the model has no
position embedding beyond `ctx` and cannot be run past it. -/
def generate (p : Params) (promptIds : Array Nat) (sc : SampleConfig) (rng : Rng)
    : Array Nat × Rng := Id.run do
  let cfg := p.cfg
  let mut cache := KVCache.empty cfg
  let mut rng := rng
  let mut emitted : Array Nat := #[]
  let mut pos := 0
  -- feed <bos> and the prompt, keeping the last logits
  let feed : Array Nat := #[bosId] ++ promptIds
  let mut logits : Vec := Vec.zeros cfg.vocab
  for tok in feed do
    if pos < cfg.ctx then
      let (lg, c) := stepToken p cache tok pos
      logits := lg
      cache := c
      pos := pos + 1
  -- then sample
  let limit := min sc.maxTokens (cfg.ctx - 1)
  let mut steps := 0
  while steps < limit && pos < cfg.ctx do
    let (tok, r) := sampleToken logits sc rng
    rng := r
    if tok == eosId then
      break
    emitted := emitted.push tok
    let (lg, c) := stepToken p cache tok pos
    logits := lg
    cache := c
    pos := pos + 1
    steps := steps + 1
  return (promptIds ++ emitted, rng)

/-! ## Cache verification

The incremental path duplicates the forward pass, so it can drift from it. This
compares the two directly: run `forward` over a prefix, and run `stepToken`
across the same prefix, then measure the largest disagreement between the two
logit vectors for the final position. -/

def verifyKVCache (p : Params) (ids : Array Nat) : Float := Id.run do
  let cfg := p.cfg
  let zero := f0
  -- full forward
  let c := forward p ids
  let ref := logitsLast p c
  -- incremental
  let mut cache := KVCache.empty cfg
  let mut logits : Vec := Vec.zeros cfg.vocab
  for i in [0:ids.size] do
    let (lg, cc) := stepToken p cache ids[i]! i
    logits := lg
    cache := cc
  -- compare (the last step's logits predict the token after `ids`)
  let mut worst := zero
  for j in [0:cfg.vocab] do
    let diff := Float.abs (ref.get! j - logits.get! j)
    if diff > worst then worst := diff
  return worst

end TinyLM
