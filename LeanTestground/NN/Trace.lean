import LeanTestground.NN.Transformer
import LeanTestground.NN.Tokenizer
import LeanTestground.NN.Driver
/-!
# Exporting a full forward pass as JSON

Every intermediate tensor a real prompt produces, written out so it can be
inspected outside Lean. This exists for teaching: a transformer drawn as boxes
and arrows hides the only thing that actually happens, which is numbers moving
between grids.

Two things are exported that the training code never needs:

* **Pre-softmax attention scores**, recomputed from the cached `q` and `k`. The
  forward pass overwrites them with probabilities in place, but the raw scores
  are what show the causal mask as a structural fact rather than a claim.
* **A perturbation trace.** The same prompt is run twice with one token
  swapped, and the per-position change in the residual stream is recorded at
  every layer. That measures information flow directly: positions before the
  swap must be bit-identical (causality), positions after it must change, and
  the change must spread with depth.
-/

namespace TinyLM

/-- Compact fixed-point float for JSON. Three decimals is well past what a
heatmap can show, and it keeps the export small. -/
private def jf (x : Float) : String :=
  if x.isNaN then "0" else
  if !x.isFinite then (if x > f0 then "9999" else "-9999") else
  if x > 9999.0 then "9999" else if x < -9999.0 then "-9999" else
  fmt x 3

/-- A `rows x cols` slice of a buffer as a JSON array of arrays. -/
private def jsonGrid (d : FloatArray) (rows cols : Nat) : String := Id.run do
  let mut parts : Array String := #[]
  for r in [0:rows] do
    let base := r * cols
    let mut row : Array String := #[]
    for c in [0:cols] do
      row := row.push (jf (d.get! (base + c)))
    parts := parts.push ("[" ++ String.intercalate "," row.toList ++ "]")
  return "[" ++ String.intercalate "," parts.toList ++ "]"

private def jsonMat (m : Mat) : String := jsonGrid m.data m.rows m.cols

private def jsonVecArr (v : Array Float) : String :=
  "[" ++ String.intercalate "," (v.toList.map jf) ++ "]"

/-- JSON string escaping. The vocabulary contains a literal `"` token, which
would otherwise close the string and produce an unparseable export. -/
private def jsonStr (s : String) : String :=
  let esc := s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    else if c.toNat < 32 then " " else String.singleton c
  "\"" ++ String.join esc ++ "\""

private def jsonStrArr (v : Array String) : String :=
  "[" ++ String.intercalate "," (v.toList.map jsonStr) ++ "]"

private def jsonNatArr (v : Array Nat) : String :=
  "[" ++ String.intercalate "," (v.toList.map toString) ++ "]"

/-! ## Attention scores before the softmax -/

/-- Recompute `qᵀk / sqrt(dHead)` per head. Masked entries are emitted as `null`
so the consumer can render the causal triangle as absence rather than as a
large negative number that merely looks like absence. -/
private def scoresJson (cfg : Config) (q k : Mat) (t : Nat) : String := Id.run do
  let d := cfg.dModel
  let dh := cfg.dHead
  let scale := f1 / Float.sqrt dh.toFloat
  let mut heads : Array String := #[]
  for hi in [0:cfg.nHeads] do
    let base := hi * dh
    let mut rows : Array String := #[]
    for ti in [0:t] do
      let mut cells : Array String := #[]
      for u in [0:t] do
        if u > ti then
          cells := cells.push "null"
        else
          let mut dot := f0
          for j in [0:dh] do
            dot := dot + q.data.get! (ti * d + base + j) * k.data.get! (u * d + base + j)
          cells := cells.push (jf (dot * scale))
      rows := rows.push ("[" ++ String.intercalate "," cells.toList ++ "]")
    heads := heads.push ("[" ++ String.intercalate "," rows.toList ++ "]")
  return "[" ++ String.intercalate "," heads.toList ++ "]"

/-- Attention probabilities from the cache, masked entries as `null`. -/
private def probsJson (cfg : Config) (probs : FloatArray) (t : Nat) : String := Id.run do
  let mut heads : Array String := #[]
  for hi in [0:cfg.nHeads] do
    let pBase := hi * t * t
    let mut rows : Array String := #[]
    for ti in [0:t] do
      let mut cells : Array String := #[]
      for u in [0:t] do
        if u > ti then cells := cells.push "null"
        else cells := cells.push (jf (probs.get! (pBase + ti * t + u)))
      rows := rows.push ("[" ++ String.intercalate "," cells.toList ++ "]")
    heads := heads.push ("[" ++ String.intercalate "," rows.toList ++ "]")
  return "[" ++ String.intercalate "," heads.toList ++ "]"

/-! ## Reconstructing the residual stream

`LayerCache` deliberately does not store the block input or the mid-residual,
because the backward pass never reads them. They are recovered here from the
embedding plus the cached branch outputs, which is exact. -/

private def blockOutputs (p : Params) (c : Cache) (li : Nat) (x : Mat)
    : Mat × Mat × Mat × Mat :=
  let l := p.layers[li]!
  let lc := c.layers[li]!
  let attnOut := lc.ctxo.mul l.wo
  let xMid := (Mat.zeros x.rows x.cols).addInto x |>.addInto attnOut
  let mlpOut := (lc.hact.mul l.w2).addRowVec l.b2
  let xOut := (Mat.zeros xMid.rows xMid.cols).addInto xMid |>.addInto mlpOut
  (attnOut, xMid, mlpOut, xOut)

/-! ## Top-k predictions -/

private def topK (logits : Vec) (k : Nat) : Array (Nat × Float) := Id.run do
  -- softmax first so the reported numbers are probabilities
  let n := logits.size
  let mut mx := fNegBig
  for i in [0:n] do
    if logits.get! i > mx then mx := logits.get! i
  let mut denom := f0
  for i in [0:n] do
    denom := denom + Float.exp (logits.get! i - mx)
  let mut pairs : Array (Nat × Float) := #[]
  for i in [0:n] do
    pairs := pairs.push (i, Float.exp (logits.get! i - mx) / denom)
  let sorted := pairs.qsort (fun a b => a.2 > b.2)
  return sorted.extract 0 (min k sorted.size)

/-! ## Perturbation: does information actually move? -/

/-- Re-run the model with the token at `swapAt` replaced, and report, for every
layer boundary, the relative L2 change in each position's residual vector.

This is the empirical form of two claims the architecture rests on. Positions
strictly before `swapAt` are unreachable and must read exactly zero. Positions
after it start at zero in the embedding (which is per-position) and become
non-zero only once attention has run. -/
private def influenceJson (p : Params) (ids : Array Nat) (swapAt : Nat)
    (newTok : Nat) : String := Id.run do
  let t := ids.size
  let d := p.cfg.dModel
  let ids2 := ids.set! swapAt newTok
  let cA := forward p ids
  let cB := forward p ids2
  -- stage 0 is the embedding, then one row per layer output
  let mut xA := embed p ids
  let mut xB := embed p ids2
  let rowNorms := fun (a b : Mat) => Id.run do
    let mut out : Array Float := #[]
    for i in [0:t] do
      let mut num := f0
      let mut den := f0
      for j in [0:d] do
        let dv := a.data.get! (i * d + j) - b.data.get! (i * d + j)
        num := num + dv * dv
        den := den + a.data.get! (i * d + j) * a.data.get! (i * d + j)
      out := out.push (if den <= f0 then f0 else Float.sqrt num / Float.sqrt den)
    return out
  let mut stages : Array String := #[jsonVecArr (rowNorms xA xB)]
  for li in [0:p.cfg.nLayers] do
    let (_, _, _, xOutA) := blockOutputs p cA li xA
    let (_, _, _, xOutB) := blockOutputs p cB li xB
    xA := xOutA
    xB := xOutB
    stages := stages.push (jsonVecArr (rowNorms xA xB))
  return "[" ++ String.intercalate "," stages.toList ++ "]"

/-! ## The export -/

def traceJson (p : Params) (v : Vocab) (prompt : String) (swapAt : Nat)
    (swapWord : String) : String := Id.run do
  let cfg := p.cfg
  let ids := #[bosId] ++ encode v prompt
  let t := min ids.size cfg.ctx
  let ids := ids.extract 0 t
  let c := forward p ids
  let logits := logitsAll p c
  let d := cfg.dModel

  -- header
  let mut out := "{\n"
  out := out ++ s!"\"dims\":\{\"T\":{t},\"d\":{d},\"heads\":{cfg.nHeads},"
  out := out ++ s!"\"dHead\":{cfg.dHead},\"dFF\":{cfg.dFF},\"layers\":{cfg.nLayers},"
  out := out ++ s!"\"vocab\":{cfg.vocab}},\n"
  out := out ++ "\"tokens\":" ++ jsonStrArr (ids.map v.decodeId) ++ ",\n"
  out := out ++ "\"tokenIds\":" ++ jsonNatArr ids ++ ",\n"

  -- embeddings: the two tables and their sum
  let mut tokRows := Vec.zeros (t * d)
  let mut posRows := Vec.zeros (t * d)
  for i in [0:t] do
    for j in [0:d] do
      tokRows := tokRows.set! (i * d + j) (p.tokEmb.data.get! (ids[i]! * d + j))
      posRows := posRows.set! (i * d + j) (p.posEmb.data.get! (i * d + j))
  out := out ++ "\"tokEmb\":" ++ jsonGrid tokRows t d ++ ",\n"
  out := out ++ "\"posEmb\":" ++ jsonGrid posRows t d ++ ",\n"
  out := out ++ "\"x0\":" ++ jsonMat (embed p ids) ++ ",\n"

  -- per-layer tensors
  let mut x := embed p ids
  let mut layerParts : Array String := #[]
  for li in [0:cfg.nLayers] do
    let lc := c.layers[li]!
    let (attnOut, xMid, mlpOut, xOut) := blockOutputs p c li x
    let mut s := "{"
    s := s ++ "\"xIn\":" ++ jsonMat x ++ ","
    s := s ++ "\"xn1\":" ++ jsonMat lc.xn1 ++ ","
    s := s ++ "\"q\":" ++ jsonMat lc.q ++ ","
    s := s ++ "\"k\":" ++ jsonMat lc.k ++ ","
    s := s ++ "\"v\":" ++ jsonMat lc.v ++ ","
    s := s ++ "\"scores\":" ++ scoresJson cfg lc.q lc.k t ++ ","
    s := s ++ "\"probs\":" ++ probsJson cfg lc.probs t ++ ","
    s := s ++ "\"ctxo\":" ++ jsonMat lc.ctxo ++ ","
    s := s ++ "\"attnOut\":" ++ jsonMat attnOut ++ ","
    s := s ++ "\"xMid\":" ++ jsonMat xMid ++ ","
    s := s ++ "\"hact\":" ++ jsonMat lc.hact ++ ","
    s := s ++ "\"mlpOut\":" ++ jsonMat mlpOut ++ ","
    s := s ++ "\"xOut\":" ++ jsonMat xOut ++ "}"
    layerParts := layerParts.push s
    x := xOut
  out := out ++ "\"layers\":[" ++ String.intercalate "," layerParts.toList ++ "],\n"

  out := out ++ "\"xF\":" ++ jsonMat c.xF ++ ",\n"

  -- top predictions at every position
  let mut preds : Array String := #[]
  for i in [0:t] do
    let mut row := Vec.zeros cfg.vocab
    for j in [0:cfg.vocab] do
      row := row.set! j (logits.data.get! (i * cfg.vocab + j))
    let tk := topK row 10
    let words := tk.map (fun (id, _) => v.decodeId id)
    let ps := tk.map (fun (_, pr) => pr)
    preds := preds.push ("{\"words\":" ++ jsonStrArr words ++ ",\"p\":" ++ jsonVecArr ps ++ "}")
  out := out ++ "\"preds\":[" ++ String.intercalate "," preds.toList ++ "],\n"

  -- perturbation
  let newTok := v.encodeWord swapWord
  out := out ++ s!"\"swap\":\{\"at\":{swapAt},\"word\":\"{swapWord}\",\"id\":{newTok}},\n"
  out := out ++ "\"influence\":" ++ influenceJson p ids swapAt newTok ++ "\n"
  out := out ++ "}\n"
  return out

def writeTrace (ckpt dataDir outPath : System.FilePath) (prompt : String)
    (swapAt : Nat) (swapWord : String) : IO Unit := do
  let (vocab, _) ← loadData dataDir
  let p ← loadCheckpoint ckpt
  let js := traceJson p vocab prompt swapAt swapWord
  IO.FS.writeFile outPath js
  IO.println s!"wrote {outPath} ({js.length} bytes)"

end TinyLM
