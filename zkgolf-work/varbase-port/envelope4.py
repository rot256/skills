exec(open('envelope.py').read().split("print(\"\\n=== VAR-BASE")[0])   # primitives (validated)
import json
def rel_layout(vlo,vhi): return half(vlo,0),half(vhi,0),half(vlo,1),half(vhi,1)
def scale(v,s): return [s*x for x in v]
def sq_bounds(lo,hi): return prod_bounds(lo,hi,lo,hi)
def umin(*vs): return [min(t) for t in zip(*vs)]
def umax(*vs): return [max(t) for t in zip(*vs)]
zero=[0]*8; Tlo,Thi=zero,dcap[:]
def resid(L,k,qb,t,tb):
    return max(abs(L[0]-(R-c)*(k+2**qb-1)-R*(t+2**tb-1)), abs(L[1]-(R-c)*k-R*t),
               abs(L[2]-(R-1)*(k+2**qb-1)+t), abs(L[3]-(R-1)*k+(t+2**tb-1)))
# ELM-complete step: S = R + T (unified slope a), R' = S + R (slope b via two-slope identity)
def step(xlo,xhi,ylo,yhi):
    # T' = mux(tInf; R, T): words in union
    txlo,txhi=umin(Tlo,xlo),umax(Thi,xhi); tylo,tyhi=umin(Tlo,ylo),umax(Thi,yhi)
    # rel1 unified: a*(yR + Ty') - (xR^2 + xR*Tx' + Tx'^2)   ;  c-branch: (yR + Ty)
    slo,shi=add(ylo,tylo),add(yhi,tyhi)
    pl,ph=prod_bounds(alo,ahi,slo,shi)
    sx=sq_bounds(xlo,xhi); px=prod_bounds(xlo,xhi,txlo,txhi); st=sq_bounds(txlo,txhi)
    rhl=add(add(sx[0],px[0]),st[0]); rhh=add(add(sx[1],px[1]),st[1])
    r1lo=umin(sub(pl,rhh),add(ylo,Tlo)); r1hi=umax(sub(ph,rhl),add(yhi,Thi))
    L1=rel_layout(r1lo,r1hi)
    # xS = a^2 - xR - Tx'
    xSlo=[SLO[i]-xhi[i]-txhi[i] for i in range(8)]; xShi=[SHI[i]-xlo[i]-txlo[i] for i in range(8)]
    # yS = a*(xR - xS) - yR
    p2=prod_bounds(alo,ahi,sub(xlo,xShi),sub(xhi,xSlo)); ySlo,yShi=sub(p2[0],yhi),sub(p2[1],ylo)
    # c-cert: xR - Tx (or 0)
    LC=rel_layout(umin(sub(xlo,Thi),zero),umax(sub(xhi,Tlo),zero))
    # z-cert: xS - xR (or 0)
    LZ=rel_layout(umin(sub(xSlo,xhi),zero),umax(sub(xShi,xlo),zero))
    # rel2: (a+b)*(xR - xS) + 2 yR  (or 0)
    p3=prod_bounds(scale(alo,2),scale(ahi,2),sub(xlo,xShi),sub(xhi,xSlo))
    L2=rel_layout(umin(add(p3[0],scale(ylo,2)),zero),umax(add(p3[1],scale(yhi,2)),zero))
    # x' = b^2 - a^2 + Tx'
    xplo=[SLO[i]-SHI[i]+txlo[i] for i in range(8)]; xphi=[SHI[i]-SLO[i]+txhi[i] for i in range(8)]
    # y' = b*(xR - x') - yR
    p4=prod_bounds(alo,ahi,sub(xlo,xphi),sub(xhi,xplo)); yplo,yphi=sub(p4[0],yhi),sub(p4[1],ylo)
    # output envelope: union {x', xS, Tx, xR, 0} / {y', yS, Ty, yR, 0}
    nxlo=umin(xplo,xSlo,Tlo,xlo,zero); nxhi=umax(xphi,xShi,Thi,xhi,zero)
    nylo=umin(yplo,ySlo,Tlo,ylo,zero); nyhi=umax(yphi,yShi,Thi,yhi,zero)
    return dict(L1=L1,LC=LC,LZ=LZ,L2=L2), (nxlo,nxhi,nylo,nyhi)
xlo,xhi,ylo,yhi=zero,dcap[:],zero,dcap[:]
hist=[]
for d in range(63):
    Ls,(xlo,xhi,ylo,yhi)=step(xlo,xhi,ylo,yhi); hist.append(Ls)
    if d in (0,1,2,10,30,61,62):
        print(d, 'xbits',max(abs(v) for v in xlo+xhi).bit_length(),'ybits',max(abs(v) for v in ylo+yhi).bit_length(),
              {k:cert_params(*L)[1::2] for k,L in Ls.items()})
lay={}
for key in ('L1','LC','LZ','L2'):
    Ls=[h[key] for h in hist[:62]]; L=(min(l[0] for l in Ls),max(l[1] for l in Ls),min(l[2] for l in Ls),max(l[3] for l in Ls))
    k,qb,t,tb=cert_params(*L); lay[key]=dict(loMin=L[0],loMax=L[1],hiMin=L[2],hiMax=L[3],kmin=k,qbits=qb,tmin=t,tbits=tb)
    print(f"steady {key}: q/t={qb}/{tb} resid bits {resid(L,k,qb,t,tb).bit_length()}")
tot=sum(v['qbits']+v['tbits'] for v in lay.values()); print("cert cost/step ~",2*tot-2*4)
json.dump(lay,open('elm.json','w'))
