# A neural network in Lean 4 that writes TinyStories

A decoder-only transformer implemented entirely in Lean 4 — tensors, tokenizer,
forward pass, hand-derived backward pass, AdamW, and sampling — with no
numerical dependencies. It trains on the
[TinyStories](https://huggingface.co/datasets/roneneldan/TinyStories) corpus and
generates children's-story prose.

There is no autodiff and no BLAS. Every gradient is derived by hand and checked
against finite differences; every matmul is a `FloatArray` loop.

## Quick start

```bash
lake build tinystories
```

Fetch a slice of the corpus (the full validation file is 19.4 MB; 4 MB is
plenty):

```bash
curl -L -H "Range: bytes=0-4194303" -o data/tinystories-slice.txt "https://huggingface.co/datasets/roneneldan/TinyStories/resolve/main/TinyStories-valid.txt"
```

Build the vocabulary and token stream:

```bash
./.lake/build/bin/tinystories prepare --corpus data/tinystories-slice.txt --data data --vocab 2048
```

Train, then sample:

```bash
./.lake/build/bin/tinystories train --data data --ckpt model.bin --steps 3000 --batch 6 --lr 0.0008
```

```bash
./.lake/build/bin/tinystories sample --ckpt model.bin --data data --n 5 --temp 0.9
```

Verify the implementation at any time:

```bash
./.lake/build/bin/tinystories check
```

## The model

| | |
|---|---|
| architecture | decoder-only transformer, pre-norm |
| normalisation | RMSNorm with learned gain |
| activation | GELU (tanh approximation) |
| attention | causal multi-head, learned position embeddings |
| default size | 4 layers, `d_model` 128, 4 heads, `d_ff` 512, context 128 |
| vocabulary | 2048 word-level types (96.5% corpus coverage) |
| parameters | 1,332,864 |
| optimizer | AdamW, decoupled decay, global-norm clipping, cosine schedule |

Word-level rather than character-level on purpose: at roughly a million
parameters, a character model would spend most of its capacity learning to
spell. TinyStories has a deliberately small vocabulary, so 2048 lowercased types
cover 96.5% of all token occurrences.

## Layout

| module | contents |
|---|---|
| `NN/Tensor.lean` | `FloatArray` matrices, three matmul kernels |
| `NN/Rng.lean` | xorshift64* PRNG, uniform and normal draws |
| `NN/Tokenizer.lean` | word-level vocabulary, encoding, detokenization |
| `NN/Model.lean` | config, parameter layout, initialisation, checkpoints |
| `NN/Transformer.lean` | forward pass, cached activations, hand-derived gradients |
| `NN/Optim.lean` | AdamW, clipping, warmup + cosine schedule |
| `NN/Train.lean` | corpus windows, gradient check, parallel mini-batches |
| `NN/Sample.lean` | KV-cached decoding, top-k / nucleus sampling |
| `NN/Driver.lean` | file I/O and the training loop |

Elsewhere in the repo:

| path | contents |
|---|---|
| `LeanTestground/Basic.lean`, `Counterexample.lean` | path/equivalence experiments in Mathlib-style Lean |
| `LeanTestground/Quantization.lean`, `BinaryAdder*.lean`, `Sweep*.lean`, `PlateauAnalysis.lean` | low-precision training; see [LOW_PRECISION_TRAINING_REPORT.md](LOW_PRECISION_TRAINING_REPORT.md) |
| `tools/` | NumPy mirror of the forward pass, steering and width-sweep scripts, grid existence searches |
| `viz/` | standalone HTML visualizations of the forward pass on sample prompts |

## Correctness

`tinystories check` runs three tests.

**The gradient check** compares the analytic gradient against central
differences at coordinates in *every one* of the 25 parameter tensors — sampling
coordinates at random across the whole model would leave individual tensors
unchecked by luck, and a wrong gradient on one weight still trains, just worse.

The convincing part is not the absolute error but how it behaves as the step
size shrinks:

| `h` | max relative error |
|---|---|
| 1e-3 | 7.5e-4 |
| 1e-4 | 7.5e-6 |
| 1e-5 | 1.3e-7 |
| 1e-6 | 8.1e-7 |

Error falls by exactly 100x per decade — the `O(h²)` signature of central
differences — and then turns around at 1e-6 when floating-point cancellation
takes over. That shape is what a correct analytic gradient looks like; a sign
error or transposed index would show a floor that does not move with `h`.

**The KV-cache check** confirms incremental decoding reproduces the full forward
pass bit-for-bit (max logit difference 0.0 at every prefix length). The
incremental path duplicates the forward pass, so it can silently drift.

**The checkpoint check** round-trips every parameter through the binary format.

## Performance notes

Getting this to run at a usable speed took three fixes, each worth more than
every micro-optimisation combined.

### 1. Float literals are not constant-folded

Lean compiles a bare `0.0` in a loop body into a fresh `Float.ofScientific`
call — `Nat` allocations and a scientific-notation decode — on *every
iteration*:

```c
v_5 = lean_unsigned_to_nat(10u);            /* inside the inner loop */
v_7 = l_Float_ofScientific(v_5, 1, ...);
v_8 = lean_float_array_set(v_a, v_i, v_7);
```

That is a 20x slowdown on a store loop: 6.8s versus 0.33s for a million stores.

**A local `let` is not a sufficient fix.** Binding `let zero := (0.0 : Float)`
at the top of a function does not keep the constant out of the loop below it —
the compiler rematerialises cheap pure bindings at their use sites. This was
visible in the generated C for `adamStep`, whose inner loop rebuilt `1.0` once
per parameter per step. Only a top-level `def`, which compiles to a cached cell,
actually works. Hence `f0`, `f1`, `fHalf` and friends in `Tensor.lean`.

Two places where this dominated the profile:

- `gelu`, being `@[inline]`, leaked its local `0.5` into the caller's loop:
  **212ms** per feed-forward activation, versus about 1ms after the fix.
- `adamStep` cost **2.26s** per training step — as much as the entire batch
  gradient — and dropped to **0.026s**, an 87x improvement.

### 2. Parallelism needs dedicated threads — but only a fixed number of them

The mini-batch is data-parallel across sequences, and two facts about Lean's
tasks pull in opposite directions here.

With the **default** task priority, a batch of 6 took exactly 6x as long as a
batch of 1 — no concurrency at all, and `LEAN_NUM_THREADS` made no difference.
Only `Task.Priority.dedicated`, which gives a task its own OS thread, actually
parallelises.

But dedicated threads are **not free to create**. Each one costs roughly 6 MB
that is never returned: 240 spawned dedicated tasks grew the resident set to
1.48 GB, against 48 MB for the same work at default priority. Spawning one per
sequence per step means about 18,000 threads over a run — and that first attempt
died with `INTERNAL PANIC: out of memory` at 8.4 GB, around step 75.

The fix is a persistent pool: `nWorkers` long-lived dedicated threads, created
once, pulling sequences off a `Std.Channel`. Six threads per run instead of
18,000, parallelism intact, and resident memory flat at about 480 MB. Results
are reordered into batch order before summing, because floating-point addition
is not associative and a loss curve that depends on thread scheduling is not one
you can debug.

### 3. Allocation churn shows up as working-set growth

Even with the pool, resident memory climbs during a long run — roughly 2 MB per
step. It is fragmentation rather than a true leak, and the shape of it is
instructive. Measured over 150 iterations each, in isolation:

| workload | peak resident |
|---|---|
| `Params.zeros` alone (same 25 sizes every time) | 22 MB |
| `sumGrads` (allocates 1.6 GB over the run) | 74 MB |
| `adamStep` | 304 MB |
| `forward` | 425 MB |
| `backward` | 785 MB |
| `forwardBackward` | 1797 MB |

Workloads that allocate the *same* sizes repeatedly recycle almost perfectly —
`sumGrads` churns 1.6 GB through a 74 MB footprint. Forward and backward
allocate many differently-sized intermediates (activation caches at `T×D`,
`T×F`, and `heads×T×T`, plus a fresh output for every matmul), and those do not
pack back into the freed holes. Memory is reclaimed under pressure, so this is
survivable rather than fatal, but a long run does drift upward.

If a run does approach the ceiling, train in segments — checkpoints are written
every `--ckptevery` steps and `--resume` picks one up. Note that resuming starts
a fresh optimizer state and schedule, so give it a lower `--lr` and short
`--warmup` to continue the decay smoothly.

### 4. Thread output buffers linearly

`FloatArray.set!` mutates in place only while the array is uniquely referenced.
The matmul kernels pass the accumulator as an argument and return it rather than
capturing it from an enclosing scope. The check that this is working: throughput
is identical at every matrix size. Hidden copying shows up as a rate that
degrades with output size.

### Result

| | before | after |
|---|---|---|
| forward (one sequence) | 1.386s | 0.555s |
| backward (one sequence) | 5.501s | 1.100s |
| `adamStep` | 2.262s | 0.026s |
| training throughput | 108 tok/s | ~395 tok/s |
| peak resident memory | 8.4 GB (OOM) | ~480 MB |

Backward now costs almost exactly 2x forward, which is what the FLOP count says
it should. Matmul kernels run at ~0.57 GFLOP/s single-threaded. Crucially, the
loss curve is bit-identical before and after every one of these changes — none
of it touched the math.

A full 3000-step run is roughly 2.3M tokens, about 2.4 epochs over the corpus
slice, and takes about 1.6 hours on six cores.

## Results

3000 steps, batch 6, context 128 — about 2.3M tokens, roughly 2.4 epochs over
the corpus slice, a bit under three hours on six cores.

| step | held-out loss | perplexity |
|---|---|---|
| 250 | 4.554 | 95.0 |
| 500 | 4.251 | 70.2 |
| 750 | 4.074 | 58.8 |
| 1000 | 3.923 | 50.6 |
| 1500 | 3.719 | 41.2 |
| 2000 | 3.565 | 35.3 |
| 2500 | 3.475 | 32.3 |
| 3000 | **3.435** | **31.0** |

Held-out perplexity 31 on a 2048-word vocabulary. Sampled at `--temp 0.8`:

> Once upon a time, there was a little boy named timmy. Timmy loved to play in
> the park. One day, timmy's mom went to the park to play with his toys. While,
> timmy's mommy was playing, timmy went on the slide, but he didn't want to go
> on the ground. They found a big, red box and a big ball. Timmy wanted to play
> with it. But timmy didn't want to try the ball to make a cake, but he hurt. He
> also said it was too sad and he didn't know what to do.

> Once upon a time there was a little girl named lucy. She had a little girl who
> loved to play outside. One day, she saw a butterfly in the garden. It was so
> shiny and beautiful. She was scared, but she found something was too special.

Prompted, with `--prompt "tom was very sad because"`:

> Tom was very sad because he knew that his friend was not very important. He had
> a great day and they got to the park. He felt happy and excited. He saw his
> mother and said," hello, mr. What are you doing?"

The register is right: the story-opening formula, named characters, dialogue
with quotation marks, simple past tense, the "One day," pivot, and occasionally
"The end." Sentences are individually well-formed. What it does not do is hold a
plot — characters get renamed mid-story (`lucy` acquires a second little girl,
`timmy` becomes `tim` becomes `joe`), and causal chains drift after a clause or
two. That is the expected failure mode at this scale, and it is exactly the gap
the TinyStories paper was measuring.

### Running it in segments

At the default size a 3000-step run does not fit in one process — see the
fragmentation note above. The run behind the table was three processes:

```bash
./.lake/build/bin/tinystories train --data data --ckpt model.bin --steps 1500 --lr 0.0008
```

```bash
./.lake/build/bin/tinystories train --data data --ckpt model.bin --resume model-step1500.bin --steps 1500 --lr 0.00044 --warmup 30
```

Each resume starts a fresh optimizer state, so the learning rate is set to where
the original cosine schedule would have been at that point. This cost nothing
measurable: held-out loss continued straight down through both splits.

## Honest expectations

This is a 1.3M-parameter model trained on 2.3M tokens of CPU compute, which is
tiny by any modern standard. It learns the register and local grammar of
TinyStories — short sentences, simple vocabulary, characters who find things and
feel happy — and it does not hold a plot together across a paragraph. The
comparison point is the smallest models in the TinyStories paper, not a modern
chat model.

The point of the exercise is that the whole stack is Lean: the gradient that
trained these weights was derived by hand and is checked against finite
differences to 1e-7.

## Deviations from GPT-2

Three, all chosen to keep the hand-written backward pass checkable:

- **RMSNorm instead of LayerNorm** — no mean subtraction, so the backward pass
  is one dot product per row instead of two.
- **Untied output head** — tying it to the embedding would save parameters but
  no FLOPs, and would route two gradients into one buffer.
- **Biases only in the feed-forward** — at this scale the others contribute
  almost nothing.
