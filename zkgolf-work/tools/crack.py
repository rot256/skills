"""Two tests.

TEST A -- can the Krull crack ever pay?
  A circuit with m=2 allocations and k=1 row is FORCED to have fibre dim >= 1
  (k < m), so it is exactly the regime where V.1's bound relaxes.  Its score is 3.
  Question: is any function it computes NOT computable by a fully-determined
  circuit of score <= 3?

TEST B -- the Jacobian corank auditor.
  d = corank of the Jacobian of the row system wrt the witness wires, at a
  generic honest witness.  Claim: d = number of allocations deletable for free
  by affine substitution."""
import itertools, sys
import numpy as np

def determined_reachable(p, max_score):
    """all f: F_p->F_p computable by a circuit with every fibre a singleton, score<=max_score"""
    out=set()
    for m in range(0, max_score+1):
        for k in range(0, max_score-m+1):
            if m+k>max_score: continue
            pts=np.array(list(itertools.product(*[range(p)]*(1+m))),dtype=np.int64)
            V=np.concatenate([np.ones((len(pts),1),dtype=np.int64),pts],axis=1)
            xs=pts[:,0]
            dim=2+m
            coeffs=np.array(list(itertools.product(*[range(p)]*dim)),dtype=np.int64)
            L=(coeffs@V.T)%p
            # enumerate all row masks
            rowmasks=set()
            for ai in range(len(coeffs)):
                PA=L[ai]
                for bi in range(ai,len(coeffs)):
                    P=(PA*L[bi])%p
                    for row in (L==P):
                        rowmasks.add(row.tobytes())
            rms=[np.frombuffer(b,dtype=bool) for b in rowmasks]
            sysmasks={np.ones(len(pts),dtype=bool).tobytes()}
            frontier=[np.ones(len(pts),dtype=bool)]
            for _ in range(k):
                nf=[]
                for s in frontier:
                    for r in rms:
                        t=s&r; b=t.tobytes()
                        if b not in sysmasks: sysmasks.add(b); nf.append(t)
                frontier=nf
            for b in sysmasks:
                t=np.frombuffer(b,dtype=bool)
                if not t.any(): continue
                cnt=np.bincount(xs[t],minlength=p)
                if (cnt!=1).any(): continue      # DETERMINED only
                xv=xs[t]
                order=np.argsort(xv)
                for ci in range(len(coeffs)):
                    out.add(tuple(int(z) for z in L[ci][t][order]))
    return out

def test_A(p, trials, seed=0):
    m,k=2,1
    rng=np.random.default_rng(seed)
    pts=np.array(list(itertools.product(*[range(p)]*(1+m))),dtype=np.int64)
    V=np.concatenate([np.ones((len(pts),1),dtype=np.int64),pts],axis=1)
    xs=pts[:,0]; dim=2+m
    coeffs=np.array(list(itertools.product(*[range(p)]*dim)),dtype=np.int64)
    L=(coeffs@V.T)%p
    det3=determined_reachable(p,3)
    print(f"  determined circuits with score<=3 reach {len(det3)} functions",flush=True)
    found=set(); notcovered=[]
    for _ in range(trials):
        A=rng.integers(0,p,dim);B=rng.integers(0,p,dim);C=rng.integers(0,p,dim)
        ok=(((V@A)%p)*((V@B)%p)-(V@C))%p==0
        if not ok.any(): continue
        cnt=np.bincount(xs[ok],minlength=p)
        if (cnt==0).any(): continue
        assert cnt.min()>=1
        for ci in range(len(coeffs)):
            vals=L[ci][ok]; xv=xs[ok]
            f=[];good=True
            for x in range(p):
                vv=vals[xv==x]
                if (vv!=vv[0]).any(): good=False;break
                f.append(int(vv[0]))
            if not good: continue
            ft=tuple(f); found.add(ft)
            if ft not in det3: notcovered.append(ft)
    print(f"  p={p}: under-determined (m=2,k=1, score 3) reached {len(found)} functions; "
          f"NOT reachable by determined score<=3: {len(set(notcovered))}",flush=True)
    for x in sorted(set(notcovered))[:5]: print("     ESCAPE:",x,flush=True)

def jac_corank(p,A,B,C,x,w):
    """corank of d(rows)/dw at witness w for input x"""
    m=len(w); v=np.array([1,x]+list(w),dtype=np.int64)
    J=[]
    for a,b,c in zip(A,B,C):
        la=int(v@a)%p; lb=int(v@b)%p
        # d/dw_i  [ la*lb - lc ] = a_i*lb + b_i*la - c_i
        J.append([(a[2+i]*lb + b[2+i]*la - c[2+i])%p for i in range(m)])
    M=np.array(J,dtype=np.int64)%p
    # rank over F_p
    M=M.copy(); r=0; rows,cols=M.shape
    for col in range(cols):
        piv=None
        for i in range(r,rows):
            if M[i,col]%p: piv=i;break
        if piv is None: continue
        M[[r,piv]]=M[[piv,r]]
        inv=pow(int(M[r,col]),p-2,p)
        M[r]=(M[r]*inv)%p
        for i in range(rows):
            if i!=r and M[i,col]%p:
                M[i]=(M[i]-M[i,col]*M[r])%p
        r+=1
        if r==rows: break
    return m-r

def test_B(p,m,k,trials,seed=1):
    """for random complete systems: does Jacobian corank predict free-slice count?"""
    rng=np.random.default_rng(seed)
    pts=np.array(list(itertools.product(*[range(p)]*(1+m))),dtype=np.int64)
    V=np.concatenate([np.ones((len(pts),1),dtype=np.int64),pts],axis=1)
    xs=pts[:,0]; W=pts[:,1:]; dim=2+m
    lams=[np.array(t) for t in itertools.product(*[range(p)]*m) if any(t)]
    agree=0; tot=0; mism=[]
    for _ in range(trials):
        A=rng.integers(0,p,(k,dim));B=rng.integers(0,p,(k,dim));C=rng.integers(0,p,(k,dim))
        ok=np.ones(len(pts),dtype=bool)
        for i in range(k):
            ok &= (((V@A[i])%p)*((V@B[i])%p)-(V@C[i]))%p==0
        cnt=np.bincount(xs[ok],minlength=p)
        if (cnt==0).any(): continue
        if cnt.min() < p-2*int(p**0.5): continue      # want uniformly positive-dim
        tot+=1
        # generic corank
        idxs=np.where(ok)[0]
        cor=max(jac_corank(p,A,B,C,int(pts[i,0]),[int(z) for z in pts[i,1:]]) for i in idxs)
        # can we slice cor times and stay complete?
        sliceable=0
        cur=ok.copy()
        for _step in range(cor):
            done=False
            for lam in lams:
                proj=(W@lam)%p
                for c in range(p):
                    sub=cur&(proj==c)
                    if (np.bincount(xs[sub],minlength=p)>0).all():
                        cur=sub; sliceable+=1; done=True; break
                if done: break
            if not done: break
        if sliceable==cor: agree+=1
        else: mism.append((cor,sliceable))
    print(f"  p={p} m={m} k={k}: {tot} uniformly-positive-dim systems; "
          f"corank-many free slices succeeded in {agree} ({100*agree/max(tot,1):.1f}%)",flush=True)
    from collections import Counter
    if mism: print("     mismatches (corank, slices achieved):",Counter(mism).most_common(6),flush=True)

if __name__=="__main__":
    print("TEST A: can m=2,k=1 (score 3, forced dim>=1) escape determined score<=3?")
    for p in [3,5]:
        test_A(p, 30000 if p==3 else 60000)
    print("\nTEST B: Jacobian corank predicts number of free affine slices")
    for (p,m,k,T) in [(5,2,1,3000),(7,2,1,3000),(11,2,1,1500),(5,3,1,2000),(5,3,2,4000),(7,3,2,3000),(7,3,1,1500),(11,3,2,800)]:
        test_B(p,m,k,T)
