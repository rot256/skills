"""Slicing lemma with a STRICT dimension proxy: every fibre must have >= p points
   (a curve over F_p has p + O(sqrt p); a finite fibre has O(1))."""
import itertools
import numpy as np
def main(p,m,k,trials,seed=7):
    rng=np.random.default_rng(seed); dim=2+m
    pts=np.array(list(itertools.product(*[range(p)]*(1+m))),dtype=np.int64)
    V=np.concatenate([np.ones((len(pts),1),dtype=np.int64),pts],axis=1)
    xs=pts[:,0]; W=pts[:,1:]
    lams=[np.array(t) for t in itertools.product(*[range(p)]*m) if any(t)]
    proj=[(W@l)%p for l in lams]
    tot=sl=un=0; fails=[]
    for _ in range(trials):
        A=rng.integers(0,p,(k,dim));B=rng.integers(0,p,(k,dim));C=rng.integers(0,p,(k,dim))
        ok=np.ones(len(pts),dtype=bool)
        for i in range(k):
            ok &= (((V@A[i])%p)*((V@B[i])%p)-(V@C[i]))%p==0
        cnt=np.bincount(xs[ok],minlength=p)
        if cnt.min() < p: continue                # STRICT: every fibre >= p points
        tot+=1
        good=False
        for pr in proj:
            for c in range(p):
                if (np.bincount(xs[ok&(pr==c)],minlength=p)>0).all(): good=True;break
            if good:break
        if good: sl+=1
        else:
            un+=1
            if len(fails)<3: fails.append((A.tolist(),B.tolist(),C.tolist(),cnt.tolist()))
    print(f"p={p} m={m} k={k}: strictly-positive-dim systems={tot}  SLICEABLE={sl}  UNSLICEABLE={un}",flush=True)
    for f in fails: print("   FAIL:",f,flush=True)
for cfg in [(5,3,2,40000),(7,3,2,40000),(11,3,2,12000),(5,3,1,4000),(7,3,1,4000),
            (5,4,3,60000),(7,4,3,30000),(5,4,2,8000),(7,4,2,6000),(5,2,1,4000)]:
    main(*cfg)
