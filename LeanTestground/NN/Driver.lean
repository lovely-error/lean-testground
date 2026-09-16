import LeanTestground.NN.Train
import LeanTestground.NN.Sample
/-!
# File I/O and the training driver

Everything in the modules below this one is pure. This is where the corpus is
read, checkpoints are written, and the training loop actually runs.

## Why tokenization is cached

Turning 4 MB of text into a token stream means walking it character by character
and hashing every word. Doing that at the start of every training run -- and
again for every resume -- is wasted minutes, and worse, it makes the vocabulary
an implicit input that could silently change. `prepare` does it once and writes
`vocab.txt` and `tokens.bin`; `train` and `sample` read those.
-/

namespace TinyLM

/-! ## Token stream serialisation

One little-endian `UInt32` per token. The vocabulary is far below 2^32, and at
four bytes a 1M-token corpus is a 4 MB file that loads in well under a second. -/

def tokensToBytes (toks : Array Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (4 * toks.size)
  for t in toks do
    let x := t.toUInt32
    for i in [0:4] do
      b := b.push (((x >>> (8 * i.toUInt32)) &&& 0xFF).toUInt8)
  return b

def tokensOfBytes (b : ByteArray) : Array Nat := Id.run do
  let n := b.size / 4
  let mut out : Array Nat := Array.emptyWithCapacity n
  for i in [0:n] do
    let o := 4 * i
    let x := (b.get! o).toNat
        ||| ((b.get! (o+1)).toNat <<< 8)
        ||| ((b.get! (o+2)).toNat <<< 16)
        ||| ((b.get! (o+3)).toNat <<< 24)
    out := out.push x
  return out

/-! ## Prepare -/

structure DataPaths where
  vocab  : System.FilePath
  tokens : System.FilePath

def dataPaths (dir : System.FilePath) : DataPaths :=
  { vocab := dir / "vocab.txt", tokens := dir / "tokens.bin" }

def prepare (corpusPath : System.FilePath) (outDir : System.FilePath) (vocabSize : Nat)
    : IO Unit := do
  IO.println s!"reading {corpusPath}"
  let raw ← IO.FS.readFile corpusPath
  let stories := splitStories raw
  IO.println s!"  {stories.size} complete stories"
  IO.println s!"building vocabulary (target {vocabSize} types)"
  let v := buildVocab stories (vocabSize - specialTokens.size)
  IO.println s!"  vocabulary size {v.size}"
  IO.println "encoding corpus"
  let stream := buildTokenStream v stories
  -- how much of the corpus survives as real words rather than <unk>
  let unkCount := stream.foldl (fun acc t => if t == unkId then acc + 1 else acc) 0
  let cov := 100.0 - 100.0 * unkCount.toFloat / stream.size.toFloat
  IO.println s!"  {stream.size} tokens, {cov}% covered (rest are <unk>)"
  let paths := dataPaths outDir
  IO.FS.createDirAll outDir
  IO.FS.writeFile paths.vocab v.toFileContents
  IO.FS.writeBinFile paths.tokens (tokensToBytes stream)
  IO.println s!"wrote {paths.vocab} and {paths.tokens}"

def loadData (dir : System.FilePath) : IO (Vocab × Array Nat) := do
  let paths := dataPaths dir
  let vtxt ← IO.FS.readFile paths.vocab
  let tb ← IO.FS.readBinFile paths.tokens
  return (Vocab.ofFileContents vtxt, tokensOfBytes tb)

/-! ## Checkpoints -/

def saveCheckpoint (path : System.FilePath) (p : Params) : IO Unit :=
  IO.FS.writeBinFile path (Params.serialize p)

def loadCheckpoint (path : System.FilePath) : IO Params := do
  let b ← IO.FS.readBinFile path
  match Params.deserialize b with
  | .ok p => return p
  | .error e => throw (IO.userError s!"could not load {path}: {e}")

/-! ## Training -/

structure TrainConfig where
  steps      : Nat := 3000
  batchSize  : Nat := 6
  baseLr     : Float := 6e-4
  warmup     : Nat := 100
  logEvery   : Nat := 10
  evalEvery  : Nat := 250
  ckptEvery  : Nat := 250
  evalBatches : Nat := 16
  /-- Worker threads. Defaults to the batch size, so each sequence in a batch
  gets its own thread; there is no benefit to exceeding the core count. -/
  workers    : Nat := 6
  seed       : UInt64 := 1234
  deriving Inhabited

/-- Format a float to a fixed number of decimals. `Float.toString` gives an
unpredictable number of digits, which makes a progress log hard to scan. -/
def fmt (x : Float) (decimals : Nat := 4) : String :=
  let neg := x < 0.0
  let x := if neg then -x else x
  let scale := Float.pow 10.0 decimals.toFloat
  let r := (x * scale + 0.5).floor
  let n := r.toUInt64.toNat
  let whole := n / (scale.toUInt64.toNat)
  let frac := n % (scale.toUInt64.toNat)
  let fracStr := String.ofList (Nat.toDigits 10 frac)
  let pad := String.ofList (List.replicate (decimals - fracStr.length) '0')
  s!"{if neg then "-" else ""}{whole}.{pad}{fracStr}"

/-- Held-out windows, taken from the tail of the stream so they share no tokens
with any training window. -/
private def buildEvalSet (stream : Array Nat) (evalStart : Nat) (ctx count : Nat)
    : Array Example := Id.run do
  let mut out : Array Example := #[]
  let mut pos := evalStart
  for _ in [0:count] do
    if pos + ctx + 1 < stream.size then
      out := out.push (windowAt stream pos ctx)
      pos := pos + ctx + 1
  return out

def train (cfg : Config) (tc : TrainConfig) (dataDir ckptPath : System.FilePath)
    (resume : Option System.FilePath) : IO Unit := do
  let (vocab, stream) ← loadData dataDir
  IO.println s!"corpus: {stream.size} tokens, vocab {vocab.size}"
  IO.println s!"model : {Config.toString cfg}"
  if vocab.size != cfg.vocab then
    IO.println s!"  note: vocab file has {vocab.size} types but config says {cfg.vocab}"
  -- last 2% is held out
  let evalStart := stream.size * 98 / 100
  let trainLimit := evalStart - cfg.ctx - 1
  let evalSet := buildEvalSet stream evalStart cfg.ctx tc.evalBatches
  IO.println s!"train tokens: {trainLimit}, eval windows: {evalSet.size}"

  let p0 ← match resume with
    | some path => do
        IO.println s!"resuming from {path}"
        loadCheckpoint path
    | none => pure (Params.init cfg (Rng.seed tc.seed))
  let mut p := p0
  let mut st := AdamState.init cfg
  let ac : AdamConfig := {}
  let mut rng := Rng.seed (tc.seed + 999)
  let tokensPerStep := tc.batchSize * cfg.ctx
  let pool ← GradPool.create (min tc.workers tc.batchSize)
  IO.println s!"workers: {pool.size}"

  IO.println ""
  IO.println "step      loss     lr        |g|      tok/s"
  -- stdout is block-buffered when redirected to a file, which would hide a
  -- multi-hour run's progress until the buffer happened to fill. Flush after
  -- every log line instead.
  let stdout ← IO.getStdout
  stdout.flush
  let tStart ← IO.monoNanosNow
  let mut lastLog := tStart

  for step in [0:tc.steps] do
    -- a fresh random batch of windows each step
    let mut batch : Array Example := #[]
    for _ in [0:tc.batchSize] do
      let (off, r) := rng.uniformNat trainLimit
      rng := r
      batch := batch.push (windowAt stream off cfg.ctx)
    let (loss, g) ← batchGrad pool p batch
    let lr := lrAt tc.baseLr step tc.warmup tc.steps
    let (p', st', gn) := adamStep p g st ac lr
    p := p'
    st := st'

    if (step + 1) % tc.logEvery == 0 then
      let now ← IO.monoNanosNow
      let secs := (now - lastLog).toFloat / 1e9
      lastLog := now
      let tps := (tc.logEvery * tokensPerStep).toFloat / secs
      IO.println s!"{step + 1}\t{fmt loss} {fmt lr 6} {fmt gn} {fmt tps 1}"
      stdout.flush

    if (step + 1) % tc.evalEvery == 0 then
      let el := evalLoss p evalSet
      IO.println (s!"  [eval] step {step + 1} held-out loss {fmt el} " ++
                  s!"perplexity {fmt (Float.exp el) 2}")
      let (ids, r) := generate p #[] { maxTokens := 60 } rng
      rng := r
      IO.println s!"  [sample] {decode vocab ids}"
      stdout.flush

    if (step + 1) % tc.ckptEvery == 0 then
      saveCheckpoint ckptPath p
      IO.println s!"  [ckpt] wrote {ckptPath}"
      stdout.flush

  pool.shutdown
  saveCheckpoint ckptPath p
  let tEnd ← IO.monoNanosNow
  IO.println s!"done in {fmt ((tEnd - tStart).toFloat / 1e9) 1}s -> {ckptPath}"

/-! ## Sampling -/

def sampleStories (ckptPath : System.FilePath) (dataDir : System.FilePath)
    (count : Nat) (sc : SampleConfig) (prompt : String) (seed : UInt64) : IO Unit := do
  let (vocab, _) ← loadData dataDir
  let p ← loadCheckpoint ckptPath
  let promptIds := if prompt.isEmpty then #[] else encode vocab prompt
  let mut rng := Rng.seed seed
  for i in [0:count] do
    let (ids, r) := generate p promptIds sc rng
    rng := r
    IO.println s!"--- {i + 1} ---"
    IO.println (decode vocab ids)
    IO.println ""

end TinyLM
