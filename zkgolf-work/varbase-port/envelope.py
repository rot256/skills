# Sparse32 envelope model. Validate against patchgravity's wideKmin, then extend to joint (x,y).
H=2**32; m=2**31; R=2**128; c=H+977; q=2**256-c; B64=2**64; wordMax=B64-1
def redCoeff(i,j,k):
    s=i+j
    if s<8: return 1 if k==s else 0
    return (1 if k==s-7 else 0) + (977 if k==s-8 else 0)
dcap=[wordMax if i%2==0 else 0 for i in range(8)]
SLO=[sum(redCoeff(i,j,k)*(0 if i==j else -m*(m-1)) for i in range(8) for j in range(8)) for k in range(8)]
SHI=[sum(redCoeff(i,j,k)*m*m for i in range(8) for j in range(8)) for k in range(8)]
def prod_bounds(alo,ahi,blo,bhi):
    """coefficient bounds of a (*) b given per-coefficient interval bounds"""
    lo=[0]*8; hi=[0]*8
    for k in range(8):
        for i in range(8):
            for j in range(8):
                r=redCoeff(i,j,k)
                if r==0: continue
                cands=[alo[i]*blo[j],alo[i]*bhi[j],ahi[i]*blo[j],ahi[i]*bhi[j]]
                lo[k]+=r*min(cands); hi[k]+=r*max(cands)
    return lo,hi
alo=[-m]*8; ahi=[m-1]*8
def half(v,side):  # lowHalf = sum_{i<4} v_i H^i ; highHalf = sum_{i>=4} v_{i} H^(i-4)
    return sum(v[i+4*side]*H**i for i in range(4))
def sub(a,b): return [x-y for x,y in zip(a,b)]
def add(a,b): return [x+y for x,y in zip(a,b)]
# --- reproduce their x-only recurrence and .wide d layouts ---
xlo=[0]*8; xhi=dcap[:]              # stateBounds 0
def wide_layout(xlo,xhi):
    # diff = embed(T.x) - x : in [ -xhi, dcap - xlo ]
    dlo=[-xhi[i] for i in range(8)]; dhi=[dcap[i]-xlo[i] for i in range(8)]
    plo,phi=prod_bounds(alo,ahi,dlo,dhi)     # one product
    wlo=[2*v for v in plo]; whi=[2*v for v in phi]   # two products summed (wideLower = 2*productLower)
    # halves minus packed y-halves (each in [0, R-1]) -> subtract up to 2*(R-1)? their loMin = lowHalf(wideLower)-2*(R-1)
    loMin=half(wlo,0)-2*(R-1); loMax=half(whi,0); hiMin=half(wlo,1)-2*(R-1); hiMax=half(whi,1)
    return loMin,loMax,hiMin,hiMax
def cert_params(loMin,loMax,hiMin,hiMax):
    # L + R*U = k*q  => k in [ (loMin+R*hiMin)/q , (loMax+R*hiMax)/q ]
    kmin=(loMin+R*hiMin)//q; kmax=-((-(loMax+R*hiMax))//q)
    qbits=(kmax-kmin).bit_length()
    # t: L - (R-c)k - R t = 0 => t = (L-(R-c)k)/R
    tmin=min((loMin-(R-c)*kk)//R for kk in (kmin,kmax)); tmax=max(-((-(loMax-(R-c)*kk))//R) for kk in (kmin,kmax))
    tbits=(tmax-tmin).bit_length()
    return kmin,qbits,tmin,tbits
print("=== reproduce patchgravity .wide d (x-only) ===")
theirs=[-126493935780483616180577,-235071471440430863991965,-361491620135168842866721]
for d in range(3):
    # state at depth d+1 (input to ext d)
    lo,hi=[0]*8,dcap[:]
    for _ in range(d+1):
        lo,hi=[SLO[i]-hi[i]-dcap[i] for i in range(8)],[SHI[i]-lo[i] for i in range(8)]
    L=wide_layout(lo,hi); kmin,qb,tmin,tb=cert_params(*L)
    print(f" d={d}: kmin={kmin}  theirs={theirs[d]}  match={kmin==theirs[d]}  qbits={qb} tbits={tb}   (theirs q={[78,79,80][d]} t={[86,87,87][d]})")
    print(f"       x-coeff hi bits: {max(hi).bit_length()}")

print("\n=== VAR-BASE joint (x,y) lazy recurrence: fused step 2R+T ===")
nativeHalf=(21888242871839275222246405745257275088548364400416034343698204186575808495617)//2
def rel_layout(vlo,vhi):
    return half(vlo,0),half(vhi,0),half(vlo,1),half(vhi,1)
def neg(v): return [-x for x in v]
def scale(v,s): return [s*x for x in v]
# state: x in [xlo,xhi], y in [ylo,yhi]; start: canonical 4x64 embedded
xlo,xhi=[0]*8,dcap[:]; ylo,yhi=[0]*8,dcap[:]
rows=[]
for d in range(80):
    # relation 1: a*(embed(Tx)-x_R) - Ty + y_R  = 0 mod q   (Ty halves each in [0,R-1], subtract at halves level)
    d1lo=[-xhi[i] for i in range(8)]; d1hi=[dcap[i]-xlo[i] for i in range(8)]
    p1lo,p1hi=prod_bounds(alo,ahi,d1lo,d1hi)
    r1lo=add(p1lo,ylo); r1hi=add(p1hi,yhi)
    L1=rel_layout(r1lo,r1hi); L1=(L1[0]-(R-1),L1[1],L1[2]-(R-1),L1[3])
    k1,q1,t1,tb1=cert_params(*L1)
    # x_S = a^2 - x_R - embed(Tx)
    xSlo=[SLO[i]-xhi[i]-dcap[i] for i in range(8)]; xShi=[SHI[i]-xlo[i] for i in range(8)]
    # relation 2: a*(x_R-x_S) + b*(x_R-x_S) - 2 y_R = 0 mod q
    d2lo=sub(xlo,xShi); d2hi=sub(xhi,xSlo)
    pAlo,pAhi=prod_bounds(alo,ahi,d2lo,d2hi)          # a*(xR-xS)
    pBlo,pBhi=pAlo,pAhi                                # b*(xR-xS) same bounds
    r2lo=sub(add(pAlo,pBlo),scale(yhi,2)); r2hi=sub(add(pAhi,pBhi),scale(ylo,2))
    L2=rel_layout(r2lo,r2hi); k2,q2,t2,tb2=cert_params(*L2)
    # x_R' = b^2 - x_S - x_R
    xlo2=[SLO[i]-xShi[i]-xhi[i] for i in range(8)]; xhi2=[SHI[i]-xSlo[i]-xlo[i] for i in range(8)]
    # y_R' = y_R + b*(x_S - x_R') - a*(x_R - x_S)
    d3lo=sub(xSlo,xhi2); d3hi=sub(xShi,xlo2)
    pClo,pChi=prod_bounds(alo,ahi,d3lo,d3hi)
    ylo2=add(add(ylo,pClo),neg(pAhi)); yhi2=add(add(yhi,pChi),neg(pAlo))
    xb=max(abs(v) for v in xlo2+xhi2).bit_length(); yb=max(abs(v) for v in ylo2+yhi2).bit_length()
    # residual check: |L| + R|U| < 2^227 needed for soundness of the field-zero => integer-zero step
    res1=max(abs(L1[0]),abs(L1[1]))+R*max(abs(L1[2]),abs(L1[3])); res2=max(abs(L2[0]),abs(L2[1]))+R*max(abs(L2[2]),abs(L2[3]))
    rows.append((d,xb,yb,q1,tb1,q2,tb2,res1.bit_length(),res2.bit_length()))
    xlo,xhi,ylo,yhi=xlo2,xhi2,ylo2,yhi2
    if xb>250 or yb>250: break
print(" d | xbits ybits | rel1 q/t | rel2 q/t | resid1 resid2 (bits; need <227 for cert soundness as written)")
for r in rows[:12]+rows[12:60:6]+rows[-2:]:
    print(f"{r[0]:2d} |  {r[1]:3d}  {r[2]:3d}  |  {r[3]:2d}/{r[4]:2d}   |  {r[5]:2d}/{r[6]:2d}   |  {r[7]:3d}    {r[8]:3d}")

print("\n=== reset period sweep (cert rows/step incl. amortised reset ~700) ===")
def period_cost(N):
    xlo,xhi=[0]*8,dcap[:]; ylo,yhi=[0]*8,dcap[:]; tot=0; tabs=[]
    for d in range(N):
        d1lo=[-xhi[i] for i in range(8)]; d1hi=[dcap[i]-xlo[i] for i in range(8)]
        p1lo,p1hi=prod_bounds(alo,ahi,d1lo,d1hi); r1lo=add(p1lo,ylo); r1hi=add(p1hi,yhi)
        L1=rel_layout(r1lo,r1hi); L1=(L1[0]-(R-1),L1[1],L1[2]-(R-1),L1[3]); k1,q1,t1,tb1=cert_params(*L1)
        xSlo=[SLO[i]-xhi[i]-dcap[i] for i in range(8)]; xShi=[SHI[i]-xlo[i] for i in range(8)]
        d2lo=sub(xlo,xShi); d2hi=sub(xhi,xSlo); pAlo,pAhi=prod_bounds(alo,ahi,d2lo,d2hi)
        r2lo=sub(add(pAlo,pAlo),scale(yhi,2)); r2hi=sub(add(pAhi,pAhi),scale(ylo,2))
        L2=rel_layout(r2lo,r2hi); k2,q2,t2,tb2=cert_params(*L2)
        xlo2=[SLO[i]-xShi[i]-xhi[i] for i in range(8)]; xhi2=[SHI[i]-xSlo[i]-xlo[i] for i in range(8)]
        d3lo=sub(xSlo,xhi2); d3hi=sub(xShi,xlo2); pClo,pChi=prod_bounds(alo,ahi,d3lo,d3hi)
        ylo2=add(add(ylo,pClo),neg(pAhi)); yhi2=add(add(yhi,pChi),neg(pAlo))
        tot+=(q1+tb1)+(q2+tb2)
        tabs.append(dict(d=d,rel1=L1+(k1,q1,t1,tb1),rel2=L2+(k2,q2,t2,tb2),xlo=xlo,xhi=xhi,ylo=ylo,yhi=yhi))
        xlo,xhi,ylo,yhi=xlo2,xhi2,ylo2,yhi2
    # reset certs: lazy - embed(canonical) = 0 mod q, canonical in [0,wordMax] at even positions
    rxlo=[xlo[i]-dcap[i] for i in range(8)]; rxhi=xhi[:]; RX=rel_layout(rxlo,rxhi); kx,qx,tx,tbx=cert_params(*RX)
    rylo=[ylo[i]-dcap[i] for i in range(8)]; ryhi=yhi[:]; RY=rel_layout(rylo,ryhi); ky,qy,ty,tby=cert_params(*RY)
    reset=2*(4+256)+(qx+tbx)+(qy+tby)+4  # witnesses+ValidP x2 + two certs + slack
    return tot, reset, (tot+reset)/N, tabs, (RX+(kx,qx,tx,tbx), RY+(ky,qy,ty,tby))
best=None
for N in range(6,25):
    tot,reset,avg,_,_=period_cost(N); print(f" N={N:2d}: certs {tot:5d} + reset {reset:4d} = {avg:7.1f}/step"); 
    if best is None or avg<best[1]: best=(N,avg)
print("BEST N =",best)
N=best[0]; tot,reset,avg,tabs,(RX,RY)=period_cost(N)
import json
json.dump(dict(N=N,tabs=[{k:(v if not isinstance(v,tuple) else list(v)) for k,v in t.items()} for t in tabs],resetX=list(RX),resetY=list(RY)),open('var_tables.json','w'))
print("resetX q/t:",RX[5],RX[7]," resetY q/t:",RY[5],RY[7])
print("wrote var_tables.json")
