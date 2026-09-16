"""A NumPy mirror of the Lean forward pass, for experiments.

The Lean implementation is the source of truth. This exists so questions like
"what happens if I add this direction to the residual stream" can be answered in
seconds instead of by writing a new Lean command each time.

`verify()` checks this mirror against a `tinystories trace` export tensor by
tensor. Nothing else in this file should be believed unless that passes.

Checkpoint layout (from Model.lean): the 8-byte magic TINYLM01, six little-endian
uint64 config fields, then every parameter as a little-endian float64 in
`Params.tensors` order.
"""
import json
import struct
import numpy as np

EPS = 1e-5
GELU_C = 0.7978845608028654
GELU_A = 0.044715


class Model:
    def __init__(self, path="model.bin"):
        b = open(path, "rb").read()
        assert b[:8] == b"TINYLM01", "not a TinyLM checkpoint"
        (self.V, self.d, self.H, self.L, self.F, self.ctx) = struct.unpack("<6Q", b[8:56])
        flat = np.frombuffer(b, dtype="<f8", offset=56)
        self.dh = self.d // self.H
        i = [0]

        def take(*shape):
            n = int(np.prod(shape))
            out = flat[i[0]:i[0] + n].reshape(shape).copy()
            i[0] += n
            return out

        self.tokEmb = take(self.V, self.d)
        self.posEmb = take(self.ctx, self.d)
        self.layers = []
        for _ in range(self.L):
            self.layers.append(dict(
                ln1g=take(self.d), wq=take(self.d, self.d), wk=take(self.d, self.d),
                wv=take(self.d, self.d), wo=take(self.d, self.d), ln2g=take(self.d),
                w1=take(self.d, self.F), b1=take(self.F),
                w2=take(self.F, self.d), b2=take(self.d)))
        self.lnFg = take(self.d)
        self.head = take(self.d, self.V)
        self.headB = take(self.V)
        assert i[0] == flat.size, f"layout mismatch: consumed {i[0]} of {flat.size}"

        self.itos = [w for w in open("data/vocab.txt", encoding="utf-8").read().split("\n") if w]
        self.stoi = {w: j for j, w in enumerate(self.itos)}

    # --- pieces -------------------------------------------------------------
    def rms(self, x, g):
        r = 1.0 / np.sqrt((x * x).mean(-1, keepdims=True) + EPS)
        return x * r * g

    def gelu(self, x):
        u = GELU_C * (x + GELU_A * x ** 3)
        return 0.5 * x * (1.0 + np.tanh(u))

    def attn(self, lp, xn):
        T = xn.shape[0]
        q, k, v = xn @ lp["wq"], xn @ lp["wk"], xn @ lp["wv"]
        out = np.zeros_like(q)
        probs = np.zeros((self.H, T, T))
        mask = np.triu(np.ones((T, T), bool), 1)
        for h in range(self.H):
            s = slice(h * self.dh, (h + 1) * self.dh)
            sc = (q[:, s] @ k[:, s].T) / np.sqrt(self.dh)
            sc = np.where(mask, -np.inf, sc)
            p = np.exp(sc - sc.max(-1, keepdims=True))
            p /= p.sum(-1, keepdims=True)
            probs[h] = p
            out[:, s] = p @ v[:, s]
        return q, k, v, probs, out

    # --- full pass ----------------------------------------------------------
    def forward(self, ids, inject=None):
        """Run the model. `inject` is an optional callback (layer, x) -> x that
        can edit the residual stream between blocks, which is how the steering
        experiments work."""
        T = len(ids)
        x = self.tokEmb[list(ids)] + self.posEmb[:T]
        tr = {"x0": x.copy(), "layers": []}
        if inject is not None:
            x = inject(-1, x)
        for li, lp in enumerate(self.layers):
            xn1 = self.rms(x, lp["ln1g"])
            q, k, v, probs, ctxo = self.attn(lp, xn1)
            attnOut = ctxo @ lp["wo"]
            xMid = x + attnOut
            xn2 = self.rms(xMid, lp["ln2g"])
            hact = self.gelu(xn2 @ lp["w1"] + lp["b1"])
            mlpOut = hact @ lp["w2"] + lp["b2"]
            x = xMid + mlpOut
            tr["layers"].append(dict(xn1=xn1, q=q, k=k, v=v, probs=probs, ctxo=ctxo,
                                     attnOut=attnOut, xMid=xMid, hact=hact,
                                     mlpOut=mlpOut, xOut=x.copy()))
            if inject is not None:
                x = inject(li, x)
        xF = self.rms(x, self.lnFg)
        tr["xF"] = xF
        tr["logits"] = xF @ self.head + self.headB
        return tr

    # --- helpers ------------------------------------------------------------
    def encode(self, text):
        return [self.stoi.get(w, 0) for w in text.split()]

    def probs_next(self, ids, inject=None):
        lg = self.forward(ids, inject)["logits"][-1]
        e = np.exp(lg - lg.max())
        return e / e.sum()

    def top(self, p, n=8):
        idx = np.argsort(-p)[:n]
        return [(self.itos[j], float(p[j])) for j in idx]


def verify(model, trace_path="trace.json", tol=2e-3):
    """Compare against the Lean export. The export is rounded to 3 decimals, so
    the tolerance is set by that rounding, not by any real disagreement."""
    T = json.load(open(trace_path))
    ids = T["tokenIds"]
    tr = model.forward(ids)
    worst = []

    def cmp(name, mine, theirs):
        a = np.asarray(mine, float)
        b = np.array([[0.0 if c is None else c for c in row] for row in theirs], float)
        worst.append((name, float(np.abs(a - b).max())))

    cmp("x0", tr["x0"], T["x0"])
    cmp("xF", tr["xF"], T["xF"])
    for li in range(model.L):
        for key in ("xn1", "q", "k", "v", "ctxo", "attnOut", "xMid", "hact", "mlpOut", "xOut"):
            cmp(f"L{li}.{key}", tr["layers"][li][key], T["layers"][li][key])
        for h in range(model.H):
            p = np.where(np.triu(np.ones((len(ids), len(ids)), bool), 1),
                         0.0, tr["layers"][li]["probs"][h])
            cmp(f"L{li}.probs[{h}]", p, T["layers"][li]["probs"][h])
    worst.sort(key=lambda t: -t[1])
    ok = worst[0][1] < tol
    return ok, worst[:5]


if __name__ == "__main__":
    m = Model()
    ok, worst = verify(m)
    print("config: V=%d d=%d H=%d L=%d F=%d ctx=%d" % (m.V, m.d, m.H, m.L, m.F, m.ctx))
    print("verify vs Lean export:", "MATCH" if ok else "MISMATCH")
    for n, e in worst:
        print("   %-16s max abs diff %.2e" % (n, e))
