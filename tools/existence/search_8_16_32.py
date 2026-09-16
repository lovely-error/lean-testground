"""Randomized search for certified adder-cell weights on coarse grids (steps 8, 16, 32).

Weights are multiples of the step in [-32, 32]. A weight vector is certified when all
8 input patterns give output pre-activations on the correct side of 0 (the `certificate`
of LeanTestground/BinaryAdder.lean, evaluated in floating point). Anything found here is
then checked exactly in Lean (see `hand8_certified` / `found16_certified` in
LeanTestground/Sweep.lean). Run: python tools/existence/search_8_16_32.py
Writes exist_search.json to the current directory.
"""
import numpy as np, sys, json, time
rng=np.random.default_rng(0)
P=np.array([[p&1,(p>>1)&1,(p>>2)&1] for p in range(8)],dtype=float)
V=np.hstack([P,np.ones((8,1))])                  # 8x4 inputs with bias
n=P.sum(1); tsum=(n%2==1); tcar=(n>=2)
def sig(z): return 0.5+z/(2*(1+np.abs(z)))
def margin(th):
    W1=th[:16].reshape(4,4); W2=th[16:].reshape(2,5)
    H=sig(V@W1.T); U=np.hstack([H,np.ones((8,1))]); Z=U@W2.T
    m0=np.where(tsum,Z[:,0],-Z[:,0]); m1=np.where(tcar,Z[:,1],-Z[:,1])
    return min(m0.min(),m1.min())
def search(s, restarts, iters):
    vals=np.arange(-32,32+1e-9,s); K=len(vals); best=-1e9; bestth=None
    for r in range(restarts):
        idx=rng.integers(0,K,26); cur=margin(vals[idx]); T=4.0
        for it in range(iters):
            j=rng.integers(26); old=idx[j]; idx[j]=rng.integers(K)
            m=margin(vals[idx])
            if m>=cur or rng.random()<np.exp((m-cur)/T): cur=m
            else: idx[j]=old
            T*=0.9995
            if cur>1e-6: return idx.copy(), cur
        if cur>best: best,bestth=cur,idx.copy()
    return None,best
# sanity: step 8 hand solution
vals8=np.arange(-32,33,8)
hand8=[16,16,16,-8, 16,16,16,-24, 8,8,8,-24, 0,0,0,0, 16,-16,32,0,-8, 0,16,0,0,-8]
print("hand step-8 margin", margin(np.array(hand8,float)))
out={}
for s in (8,16,32):
    t=time.time(); idx,m=search(s, restarts=300, iters=6000)
    vals=np.arange(-32,32+1e-9,s)
    if idx is not None:
        out[s]={"found":True,"weights":vals[idx].tolist(),"indices":idx.tolist(),"margin":m}
    else:
        out[s]={"found":False,"best_margin":m}
    print(s, out[s], round(time.time()-t,1),"s", flush=True)
json.dump(out,open("exist_search.json","w"))
