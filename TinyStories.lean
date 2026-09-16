import LeanTestground.NeuralTextGenerator
/-!
# `tinystories` -- command line entry point

    tinystories prepare  [--corpus F] [--data D] [--vocab N]
    tinystories train    [--data D] [--ckpt F] [--steps N] [--batch N]
                         [--lr X] [--dim N] [--layers N] [--heads N]
                         [--ff N] [--ctx N] [--vocab N] [--resume F]
    tinystories sample   [--ckpt F] [--data D] [--n N] [--temp X]
                         [--topk N] [--topp X] [--tokens N] [--prompt S]
                         [--seed N]
    tinystories check    -- gradient check, KV-cache equivalence, checkpoint round-trip
    tinystories bench    -- matmul and forward/backward throughput
-/

open TinyLM

/-! ## Argument parsing

A flat `--key value` scan. The `Cli` package is available here, but the flag set
is small enough that a dependency would cost more than it saves. -/

structure Args where
  map : Std.HashMap String String

def parseArgs (as : List String) : Args := Id.run do
  let mut m : Std.HashMap String String := ∅
  let mut rest := as
  while true do
    match rest with
    | k :: v :: tl =>
      if k.startsWith "--" then
        m := m.insert (k.drop 2).toString v
        rest := tl
      else
        rest := v :: tl
    | _ => break
  return { map := m }

def Args.str (a : Args) (k : String) (d : String) : String := a.map.getD k d
def Args.nat (a : Args) (k : String) (d : Nat) : Nat :=
  match a.map[k]? with
  | some v => v.toNat?.getD d
  | none => d
def Args.float (a : Args) (k : String) (d : Float) : Float :=
  match a.map[k]? with
  | some v => match Lean.Syntax.decodeScientificLitVal? v with
              | some (m, e, exp) => Float.ofScientific m e exp
              | none => v.toNat?.map Nat.toFloat |>.getD d
  | none => d

def configFromArgs (a : Args) : Config :=
  { vocab   := a.nat "vocab" Config.default.vocab
    dModel  := a.nat "dim" Config.default.dModel
    nHeads  := a.nat "heads" Config.default.nHeads
    nLayers := a.nat "layers" Config.default.nLayers
    dFF     := a.nat "ff" Config.default.dFF
    ctx     := a.nat "ctx" Config.default.ctx }

/-! ## Self-checks -/

def runCheck : IO Unit := do
  let cfg := Config.tiny
  IO.println s!"model: {Config.toString cfg}"
  IO.println ""
  IO.println "1. analytic gradient vs central differences"
  IO.println "   a correct gradient falls as h^2, then turns around when"
  IO.println "   floating-point cancellation takes over:"
  for h in [1e-3, 1e-4, 1e-5, 1e-6] do
    let r := gradCheck cfg 3 12345 h
    IO.println s!"     h={fmt h 8}  max rel err {fmt (r.maxRelErr * 1e9) 3}e-9"
  let r := gradCheck cfg 4 12345 1e-5
  IO.println s!"   checked {r.checked} coordinates across {r.perTensor.size} tensors"
  let mut worstName := ""
  let mut worstVal := f0
  for (n, e) in r.perTensor do
    if e > worstVal then
      worstVal := e
      worstName := n
  IO.println s!"   worst tensor: {worstName} at {fmt (worstVal * 1e9) 3}e-9"
  IO.println (if r.maxRelErr < 1e-5 then "   PASS" else "   FAIL")
  IO.println ""
  IO.println "2. KV-cache decoding vs full forward pass"
  let p := Params.init cfg (Rng.seed 7)
  let mut rng := Rng.seed 99
  let mut ok := true
  for len in [1, 4, 8, 16] do
    let mut ids : Array Nat := #[]
    for _ in [0:len] do
      let (t, r) := rng.uniformNat cfg.vocab; rng := r
      ids := ids.push t
    let worst := verifyKVCache p ids
    IO.println s!"     prefix {len}: max logit difference {fmt (worst * 1e15) 3}e-15"
    if worst > 1e-9 then ok := false
  IO.println (if ok then "   PASS" else "   FAIL")
  IO.println ""
  IO.println "3. checkpoint round-trip"
  let bytes := Params.serialize p
  match Params.deserialize bytes with
  | .error e => IO.println s!"   FAIL: {e}"
  | .ok p2 =>
    let a := p.tensors
    let b := p2.tensors
    let mut worst := f0
    for i in [0:a.size] do
      for j in [0:a[i]!.size] do
        let d := Float.abs (a[i]!.get! j - b[i]!.get! j)
        if d > worst then worst := d
    IO.println s!"     {bytes.size} bytes, max round-trip error {worst}"
    IO.println (if worst == f0 then "   PASS" else "   FAIL")

def runBench : IO Unit := do
  IO.println "matmul throughput (single-threaded)"
  for (m, k, n, reps) in [(64, 128, 128, 200), (128, 128, 512, 40), (128, 512, 128, 40)] do
    let a : Mat := ⟨m, k, Vec.const (m * k) 0.5⟩
    let b : Mat := ⟨k, n, Vec.const (k * n) 0.25⟩
    let t0 ← IO.monoNanosNow
    let mut acc := f0
    for _ in [0:reps] do
      acc := acc + (a.mul b).data.get! 0
    let t1 ← IO.monoNanosNow
    let secs := (t1 - t0).toFloat / 1e9
    let gf := (2 * m * k * n * reps).toFloat / secs / 1e9
    IO.println s!"  {m}x{k}x{n}: {fmt gf 3} GFLOP/s (checksum {fmt acc 1})"
  IO.println ""
  IO.println "one sequence through the default model"
  let cfg := Config.default
  let p := Params.init cfg (Rng.seed 1)
  let mut ids : Array Nat := #[]
  let mut tgts : Array (Option Nat) := #[]
  let mut rng := Rng.seed 5
  for _ in [0:cfg.ctx] do
    let (t, r) := rng.uniformNat cfg.vocab; rng := r
    ids := ids.push t
    tgts := tgts.push (some t)
  let t0 ← IO.monoNanosNow
  let c := forward p ids
  let t1 ← IO.monoNanosNow
  let dl := (crossEntropy (logitsAll p c) tgts).2
  let t2 ← IO.monoNanosNow
  let g := backward p c dl (Params.zeros cfg)
  let t3 ← IO.monoNanosNow
  IO.println s!"  forward  {fmt ((t1-t0).toFloat/1e9) 3}s"
  IO.println s!"  loss     {fmt ((t2-t1).toFloat/1e9) 3}s"
  IO.println s!"  backward {fmt ((t3-t2).toFloat/1e9) 3}s (chk {fmt (g.headB.get! 0) 6})"

/-! ## Main -/

def usage : String :=
  "usage: tinystories <prepare|train|sample|check|bench> [options]\n" ++
  "  prepare  --corpus data/tinystories-slice.txt --data data --vocab 2048\n" ++
  "  train    --data data --ckpt model.bin --steps 3000 --batch 6 --lr 0.0006\n" ++
  "  sample   --ckpt model.bin --data data --n 5 --temp 0.9 --prompt \"once upon\"\n" ++
  "  check    gradient / KV-cache / checkpoint self-tests\n" ++
  "  bench    matmul and forward/backward throughput"

def main (argv : List String) : IO Unit := do
  match argv with
  | [] => IO.println usage
  | cmd :: rest =>
    let a := parseArgs rest
    match cmd with
    | "prepare" =>
      prepare (a.str "corpus" "data/tinystories-slice.txt")
              (a.str "data" "data")
              (a.nat "vocab" 2048)
    | "train" =>
      let cfg := configFromArgs a
      let tc : TrainConfig :=
        { steps := a.nat "steps" 3000
          batchSize := a.nat "batch" 6
          baseLr := a.float "lr" 6e-4
          warmup := a.nat "warmup" 100
          logEvery := a.nat "logevery" 10
          evalEvery := a.nat "evalevery" 250
          ckptEvery := a.nat "ckptevery" 250
          workers := a.nat "workers" 6
          seed := (a.nat "seed" 1234).toUInt64 }
      let resume := a.map["resume"]?.map System.FilePath.mk
      train cfg tc (a.str "data" "data") (a.str "ckpt" "model.bin") resume
    | "sample" =>
      let sc : SampleConfig :=
        { temperature := a.float "temp" 0.9
          topK := a.nat "topk" 40
          topP := a.float "topp" 0.95
          maxTokens := a.nat "tokens" 200 }
      sampleStories (a.str "ckpt" "model.bin") (a.str "data" "data")
                    (a.nat "n" 5) sc (a.str "prompt" "")
                    (a.nat "seed" 4242).toUInt64
    | "trace" =>
      writeTrace (a.str "ckpt" "model.bin") (a.str "data" "data")
                 (a.str "out" "trace.json")
                 (a.str "prompt" "once upon a time , there was a little girl named")
                 (a.nat "swapat" 3) (a.str "swapword" "dog")
    | "check" => runCheck
    | "bench" => runBench
    | _ => IO.println usage
