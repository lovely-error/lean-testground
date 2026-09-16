"""Can a handful of numbers make the model tell a different kind of story?

Builds a concept direction in the residual stream and adds it at every
generation step, then measures whether the resulting stories actually change
topic -- rather than just emitting the target word once and moving on.

Two ways of getting the direction are compared, because they answer different
questions:

* `contrast` -- the difference between the stream on a prompt containing the
  concept and the same prompt without it. This is a direction the model itself
  uses, discovered from its own activations.
* `unembed`  -- the output-matrix column for the target token. This is the
  direction that most directly raises that one word's logit, and is included as
  a baseline: if only this works, the effect is lexical rather than thematic.
"""
import sys
import numpy as np
from probe import Model

RNG = np.random.default_rng(0)


def sample(m, ids, n=60, temp=0.9, topk=40, inject=None, rng=RNG):
    ids = list(ids)
    for _ in range(n):
        p = m.probs_next(ids, inject=inject)
        p[0] = 0.0                      # never emit <unk>
        p[1] = 0.0                      # never emit <bos>
        idx = np.argsort(-p)[:topk]
        q = p[idx] ** (1.0 / temp)
        q = q / q.sum()
        t = int(rng.choice(idx, p=q))
        if t == 2:                      # <eos>
            break
        ids.append(t)
    return ids


def contrast_dir(m, word, neutral, layer, template="once upon a time there was a {}"):
    """Difference of residual streams, averaged over positions."""
    a = [1] + m.encode(template.format(word))
    b = [1] + m.encode(template.format(neutral))
    n = min(len(a), len(b))
    xa = m.forward(a)["layers"][layer]["xOut"][:n]
    xb = m.forward(b)["layers"][layer]["xOut"][:n]
    v = (xa - xb).mean(0)
    return v / (np.linalg.norm(v) + 1e-9)


def unembed_dir(m, word):
    v = m.head[:, m.stoi[word]].copy()
    return v / (np.linalg.norm(v) + 1e-9)


def injector(v, alpha, layer, last_only=False):
    def inj(li, x):
        if li != layer:
            return x
        x = x.copy()
        if last_only:
            x[-1] = x[-1] + alpha * v
        else:
            x = x + alpha * v
        return x
    return inj


def topic_rate(m, stories, words):
    """Fraction of stories mentioning any of `words`, and mean mentions."""
    hits, total = 0, 0
    for s in stories:
        ws = [m.itos[i] for i in s]
        c = sum(ws.count(w) for w in words)
        total += c
        hits += (c > 0)
    return hits / len(stories), total / len(stories)


def run(target="elephant", neutral="boy", layer=2, alphas=(0, 2, 4, 6, 8, 12),
        n_stories=12, mode="contrast", prompt="once upon a time"):
    m = Model()
    v = contrast_dir(m, target, neutral, layer) if mode == "contrast" else unembed_dir(m, target)
    base = [1] + m.encode(prompt)
    related = [target, target + "s"]
    print(f"\n=== mode={mode}  target={target!r}  layer={layer+1}  "
          f"direction is {v.size} numbers ({100*v.size/1332864:.3f}% of the model) ===")
    out = {}
    for a in alphas:
        rng = np.random.default_rng(1234)
        stories = [sample(m, base, n=55, inject=injector(v, a, layer), rng=rng)
                   for _ in range(n_stories)]
        rate, mean = topic_rate(m, stories, related)
        texts = [" ".join(m.itos[i] for i in s[1:]) for s in stories]
        out[a] = (rate, mean, texts)
        print(f"  alpha={a:>3}  stories mentioning {target}: {rate*100:5.1f}%   "
              f"mean mentions/story: {mean:4.2f}")
    return m, out


if __name__ == "__main__":
    target = sys.argv[1] if len(sys.argv) > 1 else "elephant"
    m, res = run(target=target, mode="contrast")
    run(target=target, mode="unembed")
