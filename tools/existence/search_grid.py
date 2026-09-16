"""Randomized search for certified adder-cell weights on a grid, for a chosen activation.

Weights are multiples of the grid step in [-32, 32]. A weight vector is certified when all
8 input patterns give output pre-activations on the correct side of 0 (the `certificate` of
LeanTestground/BinaryAdder.lean, evaluated in floating point). Candidates found here should be
checked exactly in Lean.

Activations:
  softsign  1/2 + z/(2(1+|z|))   (BinaryAdder.lean)
  bump      1/2 + z/(1+z^2)      (SweepBump.lean)
  rat2      2z/(1+z^2)           (SweepRat2.lean; outputs read by sign, which is the same test)

The activation is applied in the hidden layer; the output is judged by the sign of its
pre-activation, which matches the certificate for every activation above.

Run: python tools/existence/search_grid.py --act bump --steps 16 8 4 2 1
Prints one JSON line per step and writes search_grid_<act>.json to the current directory.
"""
import argparse, json, time
import numpy as np

ACTS = {
    "softsign": lambda z: 0.5 + z / (2 * (1 + np.abs(z))),
    "bump": lambda z: 0.5 + z / (1 + z * z),
    "rat2": lambda z: 2 * z / (1 + z * z),
}

P = np.array([[p & 1, (p >> 1) & 1, (p >> 2) & 1] for p in range(8)], dtype=float)
V = np.hstack([P, np.ones((8, 1))])
N = P.sum(1)
TSUM, TCAR = (N % 2 == 1), (N >= 2)


def margins(act, th):
    W1 = th[:16].reshape(4, 4); W2 = th[16:].reshape(2, 5)
    U = np.hstack([act(V @ W1.T), np.ones((8, 1))]); Z = U @ W2.T
    return np.concatenate([np.where(TSUM, Z[:, 0], -Z[:, 0]), np.where(TCAR, Z[:, 1], -Z[:, 1])])


def search(act, step, restarts, iters, rng):
    vals = np.arange(-32, 32 + 1e-9, step); K = len(vals)
    best = (-np.inf, None)
    for r in range(restarts):
        # half the restarts start near zero, where a non-saturating activation is most expressive
        if r % 2:
            mid = K // 2; idx = np.clip(mid + rng.integers(-2, 3, 26), 0, K - 1)
        else:
            idx = rng.integers(0, K, 26)
        m = margins(act, vals[idx]); cur = np.minimum(m, 2).sum(); T = 3.0
        for _ in range(iters):
            j = rng.integers(26); old = idx[j]; idx[j] = rng.integers(K)
            m2 = margins(act, vals[idx]); sc = np.minimum(m2, 2).sum()
            if sc >= cur or rng.random() < np.exp((sc - cur) / T):
                cur, m = sc, m2
            else:
                idx[j] = old
            T *= 0.999
            if m.min() > 1e-6:
                return {"found": True, "min_margin": float(m.min()), "weights": vals[idx].tolist(),
                        "indices": idx.tolist(), "restarts": r + 1}
        if m.min() > best[0]:
            best = (float(m.min()), vals[idx].tolist())
    return {"found": False, "best_min_margin": best[0], "restarts": restarts}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--act", choices=ACTS, default="softsign")
    ap.add_argument("--steps", type=float, nargs="+", default=[16, 8, 4, 2, 1])
    ap.add_argument("--restarts", type=int, default=2000)
    ap.add_argument("--iters", type=int, default=4000)
    ap.add_argument("--seed", type=int, default=0)
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    out = {}
    for s in a.steps:
        t = time.time()
        r = search(ACTS[a.act], s, a.restarts, a.iters, rng)
        r["secs"] = round(time.time() - t, 1)
        out[str(s)] = r
        print(json.dumps({"act": a.act, "step": s, **r}), flush=True)
    json.dump(out, open(f"search_grid_{a.act}.json", "w"))


if __name__ == "__main__":
    main()
