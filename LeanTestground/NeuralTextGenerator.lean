import LeanTestground.NN.Tensor
import LeanTestground.NN.Rng
import LeanTestground.NN.Tokenizer
import LeanTestground.NN.Model
import LeanTestground.NN.Transformer
import LeanTestground.NN.Optim
import LeanTestground.NN.Train
import LeanTestground.NN.Sample
import LeanTestground.NN.Driver
import LeanTestground.NN.Trace
/-!
# A neural text generator in Lean 4

A decoder-only transformer -- tensors, tokenizer, forward pass, hand-written
backward pass, AdamW and sampling -- implemented in Lean with no external
numerical dependencies, and trained on TinyStories.

Read the modules in this order:

| module       | contents                                                  |
|--------------|-----------------------------------------------------------|
| `Tensor`     | `FloatArray` matrices and the matmul kernels               |
| `Rng`        | xorshift PRNG, uniform and normal draws                    |
| `Tokenizer`  | word-level vocabulary, encoding, detokenization            |
| `Model`      | config, parameter layout, initialisation, checkpoints      |
| `Transformer`| forward pass, cached activations, hand-derived gradients   |
| `Optim`      | AdamW, gradient clipping, warmup + cosine schedule         |
| `Train`      | corpus windows, gradient check, parallel mini-batches      |
| `Sample`     | KV-cached incremental decoding, top-k / nucleus sampling   |
| `Driver`     | file I/O and the training loop                             |
| `Trace`      | exports a full forward pass as JSON, for inspection        |
-/
