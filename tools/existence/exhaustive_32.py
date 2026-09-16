"""Exhaustive check that no certified weights exist on the step-32 grid (values -32, 0, 32).

Enumerates all multisets of 4 distinct hidden units against all 3^5 output weight vectors
for both outputs, requiring every output pre-activation to clear 1e-9. Floating point, not
a Lean proof; referenced from LeanTestground/Sweep.lean. Takes a few minutes.
Run: python tools/existence/exhaustive_32.py [softsign|bump]
Writes exist_exhaustive32_<act>.json to the current directory.
"""
import numpy as np, itertools, time, json, sys
P=np.array([[p&1,(p>>1)&1,(p>>2)&1] for p in range(8)],dtype=float)
V=np.hstack([P,np.ones((8,1))]); n=P.sum(1)
tsum=(n%2==1); tcar=(n>=2)
ACT = sys.argv[1] if len(sys.argv) > 1 else "softsign"
def sig(z): return 0.5+z/(2*(1+np.abs(z))) if ACT == "softsign" else 0.5+z/(1+z*z)
TOL=1e-9
def exhaustive(s):
    vals=np.arange(-32,32+1e-9,s)
    units=np.array(list(itertools.product(vals,repeat=4)))          # hidden unit weights
    H=sig(units@V.T)                                                  # (#units, 8)
    Hr=np.round(H,12); _,keep=np.unique(Hr,axis=0,return_index=True)
    H=H[keep]; units=units[keep]; M=len(H)
    Wout=np.array(list(itertools.product(vals,repeat=5)))            # (#w, 5)
    combos=itertools.combinations_with_replacement(range(M),4)
    total=0; found=None; t=time.time()
    while True:
        chunk=np.array(list(itertools.islice(combos,20000)))
        if len(chunk)==0: break
        total+=len(chunk)
        U=np.concatenate([H[chunk].transpose(0,2,1), np.ones((len(chunk),8,1))],axis=2)  # (c,8,5)
        Z=np.einsum('wj,cpj->cwp',Wout,U)                             # (c,w,8)
        oks=np.all(np.where(tsum,Z,-Z)>TOL,axis=2).any(axis=1)
        okc=np.all(np.where(tcar,Z,-Z)>TOL,axis=2).any(axis=1)
        both=np.nonzero(oks&okc)[0]
        if len(both):
            c=chunk[both[0]]; U1=U[both[0]]; Zs=Wout@U1.T
            ws=Wout[np.all(np.where(tsum,Zs,-Zs)>TOL,axis=1)][0]
            wc=Wout[np.all(np.where(tcar,Zs,-Zs)>TOL,axis=1)][0]
            found={"hidden":units[c].tolist(),"sum":ws.tolist(),"carry":wc.tolist()}
            break
    return {"step":s,"distinct_units":int(M),"hidden_sets_checked":total,"output_weight_vectors":len(Wout),"found":found,"secs":round(time.time()-t,1)}
r=exhaustive(32); r["act"]=ACT; print(r, flush=True)
json.dump(r,open(f"exist_exhaustive32_{ACT}.json","w"))
