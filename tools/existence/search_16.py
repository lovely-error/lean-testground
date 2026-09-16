"""Randomized search with a smoothed objective for the step-16 grid (values -32..32 by 16).

Produced the weights of `found16` in LeanTestground/Sweep.lean, which `found16_certified`
checks exactly. Run: python tools/existence/search_16.py
Writes exist_search16.json to the current directory.
"""
import numpy as np, json, time
rng=np.random.default_rng(1)
P=np.array([[p&1,(p>>1)&1,(p>>2)&1] for p in range(8)],dtype=float)
V=np.hstack([P,np.ones((8,1))]); n=P.sum(1); tsum=(n%2==1); tcar=(n>=2)
def sig(z): return 0.5+z/(2*(1+np.abs(z)))
def margins(th):
    W1=th[:16].reshape(4,4); W2=th[16:].reshape(2,5)
    U=np.hstack([sig(V@W1.T),np.ones((8,1))]); Z=U@W2.T
    return np.concatenate([np.where(tsum,Z[:,0],-Z[:,0]),np.where(tcar,Z[:,1],-Z[:,1])])
vals=np.arange(-32,33,16); K=len(vals); best=(-1e9,None); t=time.time()
for r in range(3000):
    idx=rng.integers(0,K,26); m=margins(vals[idx]); cur=np.minimum(m,2).sum(); T=3.0
    for it in range(4000):
        j=rng.integers(26); old=idx[j]; idx[j]=rng.integers(K)
        m2=margins(vals[idx]); sc=np.minimum(m2,2).sum()
        if sc>=cur or rng.random()<np.exp((sc-cur)/T): cur=sc; m=m2
        else: idx[j]=old
        T*=0.999
        if m.min()>1e-6: break
    if m.min()>best[0]: best=(m.min(),vals[idx].tolist())
    if m.min()>1e-6: break
print({"step":16,"found":best[0]>1e-6,"best_min_margin":float(best[0]),"weights":best[1],"restarts":r+1,"secs":round(time.time()-t,1)})
json.dump({"found":bool(best[0]>1e-6),"best_min_margin":float(best[0]),"weights":best[1],"restarts":r+1},open("exist_search16.json","w"))
