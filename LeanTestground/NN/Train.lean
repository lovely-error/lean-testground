import LeanTestground.NN.Transformer
import LeanTestground.NN.Optim
import LeanTestground.NN.Tokenizer
import Std.Sync.Channel
/-!
# Data pipeline, gradient check, and the training loop

## Parallelism

The single-threaded matmul runs at roughly 0.57 GFLOP/s, which is not enough to
train anything interesting in an evening. The mini-batch is therefore split
across `Task`s: each sequence's forward and backward pass is a pure function
into its own gradient buffer, so they can run concurrently with no
synchronisation at all, and the results are summed afterwards.

Sequence-level data parallelism rather than parallelism inside the matmul: the
work per task is seconds rather than microseconds, so scheduling overhead
disappears, and the kernels stay single-threaded and easy to reason about.

### Why a persistent pool rather than `Task.spawn` per sequence

Two facts about Lean's tasks forced this design, and they pull in opposite
directions:

1. **Default-priority tasks do not run concurrently here.** A batch of 6 took
   exactly 6x as long as a batch of 1, and `LEAN_NUM_THREADS` made no
   difference. Only `Task.Priority.dedicated`, which gives a task its own OS
   thread, actually parallelises.

2. **Dedicated threads are not free to create.** Each one costs roughly 6 MB
   that is never returned: 240 spawned dedicated tasks grew the resident set to
   1.48 GB, against 48 MB for the same work at default priority. Spawning one
   per sequence per step means ~18000 threads over a training run, and the first
   attempt at that died with `INTERNAL PANIC: out of memory` around step 75,
   having reached 8.4 GB.

So: dedicated threads, but a fixed number of them, created once and reused for
the whole run. `GradPool` is `nWorkers` long-lived workers pulling sequences off
a channel -- 6 threads per run instead of 18000, with the parallelism intact.
-/

namespace TinyLM

/-! ## Corpus

TinyStories ships as stories separated by `<|endoftext|>`. Each becomes
`<bos> ... <eos>`, and the whole corpus is concatenated into one token stream
that training samples fixed-length windows from. Windows may straddle a story
boundary; that is deliberate, since it is what teaches the model that `<eos>`
is followed by a fresh start rather than more of the same story. -/

def storySeparator : String := "<|endoftext|>"

/-- Split raw corpus text into stories, dropping the first and last fragments,
which a byte-range download will have truncated mid-story. -/
def splitStories (raw : String) : Array String :=
  let parts := (raw.splitOn storySeparator).toArray
  let parts := if parts.size >= 3 then parts.extract 1 (parts.size - 1) else parts
  parts.filter (fun s => s.length > 32)

/-- Encode every story into one flat token stream. -/
def buildTokenStream (v : Vocab) (stories : Array String) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for s in stories do
    out := out.push bosId
    for id in encode v s do
      out := out.push id
    out := out.push eosId
  return out

/-- One training example: `ctx` inputs and the `ctx` tokens that should follow. -/
structure Example where
  ids     : Array Nat
  targets : Array (Option Nat)
  deriving Inhabited

/-- Cut a window `[start, start + ctx]` out of the stream. -/
def windowAt (stream : Array Nat) (start ctx : Nat) : Example := Id.run do
  let mut ids : Array Nat := #[]
  let mut tgts : Array (Option Nat) := #[]
  for i in [0:ctx] do
    ids := ids.push stream[start + i]!
    tgts := tgts.push (some stream[start + i + 1]!)
  return { ids, targets := tgts }

/-! ## Gradient check

Central differences against the analytic gradient. This is the only real defence
against a sign error or a transposed index in `Transformer.lean`, both of which
produce a model that still trains -- just to a worse loss -- and so would
otherwise go unnoticed.

Checked on `Config.tiny`, at randomly chosen coordinates, with a relative error
tolerance appropriate for `h = 1e-4` in double precision. -/

def lossAt (p : Params) (ex : Example) : Float :=
  let c := forward p ex.ids
  let logits := logitsAll p c
  (crossEntropy logits ex.targets).1

/-- Human-readable name for each entry of `Params.tensors`, so a failure points
at a specific weight rather than an index. -/
def tensorNames (cfg : Config) : Array String := Id.run do
  let mut n : Array String := #["tokEmb", "posEmb"]
  for l in [0:cfg.nLayers] do
    for nm in ["ln1g", "wq", "wk", "wv", "wo", "ln2g", "w1", "b1", "w2", "b2"] do
      n := n.push s!"L{l}.{nm}"
  return n ++ #["lnFg", "head", "headB"]

structure GradCheckResult where
  maxRelErr : Float
  checked   : Nat
  worst     : String
  /-- Per-tensor worst relative error, in `Params.tensors` order. -/
  perTensor : Array (String × Float)
  deriving Inhabited

/-- Check `coordsPer` coordinates in *every* parameter tensor.

Sampling coordinates uniformly at random across the whole model would leave
individual tensors unchecked by luck -- and a wrong gradient on, say, `wk` alone
still trains, just worse. Visiting every tensor is what makes this a real test.

Coordinates that the sequence does not exercise (an embedding row for a token
that never appears) have a true gradient of exactly zero and are skipped rather
than counted as agreement. -/
def gradCheck (cfg : Config) (coordsPer : Nat) (seed : UInt64) (h : Float := 1e-4)
    : GradCheckResult :=
  Id.run do
    let zero := f0
    let two := f2
    let mut rng := Rng.seed seed
    let p := Params.init cfg rng
    let t := cfg.ctx
    let mut ids : Array Nat := #[]
    let mut tgts : Array (Option Nat) := #[]
    for _ in [0:t] do
      let (a, r) := rng.uniformNat cfg.vocab; rng := r
      ids := ids.push a
    for _ in [0:t] do
      let (a, r) := rng.uniformNat cfg.vocab; rng := r
      tgts := tgts.push (some a)
    let ex : Example := { ids, targets := tgts }
    let (_, g) := forwardBackward p ex.ids ex.targets (Params.zeros cfg)
    let gts := g.tensors
    let pts := p.tensors
    let names := tensorNames cfg
    let mut maxRel := zero
    let mut worst := "none"
    let mut checked := 0
    let mut perTensor : Array (String × Float) := #[]
    for ti in [0:pts.size] do
      let tensor := pts[ti]!
      let mut tensorWorst := zero
      let mut tries := 0
      let mut done := 0
      -- keep drawing until `coordsPer` coordinates with a non-trivial gradient
      -- have been checked, or we give up looking
      while done < coordsPer && tries < coordsPer * 20 && tensor.size > 0 do
        tries := tries + 1
        let (ci, r) := rng.uniformNat tensor.size; rng := r
        let analytic := gts[ti]!.get! ci
        if Float.abs analytic < 1e-9 then
          continue
        let orig := tensor.get! ci
        let pPlus := Params.ofTensors cfg (pts.set! ti (tensor.set! ci (orig + h)))
        let lPlus := lossAt pPlus ex
        let pMinus := Params.ofTensors cfg (pts.set! ti (tensor.set! ci (orig - h)))
        let lMinus := lossAt pMinus ex
        let numeric := (lPlus - lMinus) / (two * h)
        let denom := Float.abs numeric + Float.abs analytic
        let rel := if denom < 1e-12 then zero
                   else Float.abs (numeric - analytic) / denom
        if rel > tensorWorst then tensorWorst := rel
        if rel > maxRel then
          maxRel := rel
          worst := s!"{names[ti]!}[{ci}]: analytic {analytic} numeric {numeric}"
        checked := checked + 1
        done := done + 1
      perTensor := perTensor.push (names[ti]!, tensorWorst)
    return { maxRelErr := maxRel, checked, worst, perTensor }

/-! ## The worker pool -/

/-- A sequence to differentiate, tagged with its slot in the batch. `none` is
the shutdown signal. -/
abbrev GradJob := Option (Nat × Params × Example)

/-- `(slot, loss, gradient)`. -/
abbrev GradRes := Nat × Float × Params

structure GradPool where
  jobs    : Std.Channel.Sync GradJob
  results : Std.Channel.Sync GradRes
  workers : Array (Task (Except IO.Error Unit))
  size    : Nat

/-- Pull sequences off the job channel until told to stop. The gradient buffer
is allocated per job rather than shared, so workers never touch each other's
memory and no locking is needed anywhere. -/
private partial def gradWorker (jobs : Std.Channel.Sync GradJob)
    (results : Std.Channel.Sync GradRes) : IO Unit := do
  match ← jobs.recv with
  | none => return ()
  | some (slot, p, ex) =>
    let (loss, g) := forwardBackward p ex.ids ex.targets (Params.zeros p.cfg)
    results.send (slot, loss, g)
    gradWorker jobs results

namespace GradPool

/-- Start `n` worker threads. Create one of these per training run, not per
step -- see the note at the top of this file. -/
def create (n : Nat) : IO GradPool := do
  let jobs : Std.Channel.Sync GradJob ← Std.Channel.Sync.new
  let results : Std.Channel.Sync GradRes ← Std.Channel.Sync.new
  let mut workers := #[]
  for _ in [0:n] do
    workers := workers.push (← IO.asTask (gradWorker jobs results) Task.Priority.dedicated)
  return { jobs, results, workers, size := n }

/-- Send one shutdown signal per worker and wait for them all to finish. -/
def shutdown (pool : GradPool) : IO Unit := do
  for _ in [0:pool.size] do
    pool.jobs.send none
  for w in pool.workers do
    match w.get with
    | .ok _ => pure ()
    | .error e => IO.eprintln s!"worker failed: {e}"

end GradPool

/-! ## Mini-batch gradient -/

/-- Sum a batch of gradients into one. -/
def sumGrads (cfg : Config) (gs : Array Params) : Params := Id.run do
  if gs.size == 0 then
    return Params.zeros cfg
  let mut acc := gs[0]!.tensors
  for gi in [1:gs.size] do
    let ts := gs[gi]!.tensors
    let mut next : Array FloatArray := #[]
    for idx in [0:acc.size] do
      next := next.push (Vec.addInto acc[idx]! ts[idx]!)
    acc := next
  return Params.ofTensors cfg acc

/-- Forward and backward over a whole mini-batch, in parallel. Returns the mean
loss and the summed-then-averaged gradient.

Results come back in completion order, so they are placed back into batch order
before summing. Floating-point addition is not associative, and a run whose loss
curve depends on thread scheduling is not one you can debug. -/
def batchGrad (pool : GradPool) (p : Params) (batch : Array Example)
    : IO (Float × Params) := do
  let cfg := p.cfg
  for slot in [0:batch.size] do
    pool.jobs.send (some (slot, p, batch[slot]!))
  let mut slots : Array (Option (Float × Params)) :=
    Array.replicate batch.size none
  for _ in [0:batch.size] do
    let (slot, loss, g) ← pool.results.recv
    slots := slots.set! slot (some (loss, g))
  let mut total := f0
  let mut grads : Array Params := #[]
  for entry in slots do
    match entry with
    | some (l, g) => total := total + l; grads := grads.push g
    | none => pure ()
  let summed := sumGrads cfg grads
  -- average over the batch
  let n := batch.size
  let scale := f1 / n.toFloat
  let ts := summed.tensors
  let mut scaled : Array FloatArray := #[]
  for t in ts do
    let mut t := t
    for i in [0:t.size] do
      t := t.set! i (t.get! i * scale)
    scaled := scaled.push t
  return (total * scale, Params.ofTensors cfg scaled)

/-! ## Evaluation -/

/-- Mean cross-entropy over a fixed set of held-out windows.

Sequential on purpose. Evaluation runs a few times per training run rather than
every step, so the handful of seconds it costs is not worth either spawning
throwaway threads (which leak, see above) or widening the pool's job type. -/
def evalLoss (p : Params) (batch : Array Example) : Float := Id.run do
  if batch.size == 0 then
    return f0
  let mut total := f0
  for ex in batch do
    total := total + lossAt p ex
  return total / batch.size.toFloat

end TinyLM
