"""Exhaustive: for every function f: F_p -> F_p, compare
     best score over ALL sound+complete R1CS  vs  best score over circuits where
     every witness is UNIQUELY DETERMINED by the input.
   Score = m (allocations) + k (rows). Output = any affine functional (free)."""
import itertools, sys
from collections import defaultdict

def build(p,m):
    pts=[t for t in itertools.product(*[range(p)]*(1+m))]
    N=len(pts)
    V=[(1,)+t for t in pts]
    dim=2+m
    coeffs=[c for c in itertools.product(*[range(p)]*dim)]
    L=[[sum(c[j]*v[j] for j in range(dim))%p for v in V] for c in coeffs]
    seen=set(); reps=[]
    for i,c in enumerate(coeffs):
        if not any(c) or c in seen: continue
        for s in range(1,p): seen.add(tuple((cj*s)%p for cj in c))
        reps.append(i)
    masks=set(); zero=coeffs.index((0,)*dim)
    for ai in [zero]+reps:
        LA=L[ai]
        for bi in range(len(coeffs)):
            LB=L[bi]; P=[(LA[t]*LB[t])%p for t in range(N)]
            for LC in L:
                mk=0
                for t in range(N):
                    if LC[t]==P[t]: mk|=1<<t
                masks.add(mk)
    return pts,N,coeffs,L,sorted(masks)

def sweep(p,mmax,kmax,cap=300000):
    best=defaultdict(lambda:[99,99])
    for m in range(0,mmax+1):
        pts,N,coeffs,L,masks=build(p,m)
        print("p=%d m=%d: %d one-row sets, N=%d"%(p,m,len(masks),N),flush=True)
        full=(1<<N)-1
        systems={full:0}; frontier=[full]
        for k in range(1,kmax+1):
            nf=[]
            for s in frontier:
                for mk in masks:
                    t=s&mk
                    if t not in systems: systems[t]=k; nf.append(t)
            frontier=nf
            print("   k=%d: %d systems"%(k,len(systems)),flush=True)
            if len(systems)>cap: break
        xs=[t[0] for t in pts]
        for s,k in systems.items():
            if s==0: continue
            fib=defaultdict(list)
            ss=s; t=0
            while ss:
                if ss&1: fib[xs[t]].append(t)
                ss>>=1; t+=1
            if len(fib)<p: continue
            det=all(len(v)==1 for v in fib.values())
            score=m+k
            for LC in L:
                f=[]; ok=True
                for x in range(p):
                    vs={LC[i] for i in fib[x]}
                    if len(vs)>1: ok=False;break
                    f.append(vs.pop())
                if not ok: continue
                ft=tuple(f); e=best[ft]
                if score<e[0]: e[0]=score
                if det and score<e[1]: e[1]=score
    return best

if __name__=="__main__":
    p=int(sys.argv[1]);mm=int(sys.argv[2]);kk=int(sys.argv[3])
    best=sweep(p,mm,kk)
    gaps=[(f,v) for f,v in best.items() if v[0]<v[1]]
    print("\nreachable functions: %d"%len(best))
    print("UNDER-DETERMINED strictly cheaper: %d"%len(gaps))
    for f,v in sorted(gaps)[:30]: print("   f=",f," any=",v[0]," det=",v[1])
