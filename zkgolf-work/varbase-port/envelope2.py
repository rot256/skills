exec(open('envelope.py').read().split("print(\"\\n=== VAR-BASE")[0])   # reuse primitives + validated helpers

def rel_layout(vlo,vhi): return half(vlo,0),half(vhi,0),half(vlo,1),half(vhi,1)
def neg(v): return [-x for x in v]
def scale(v,s): return [s*x for x in v]
print("=== CORRECTED var-base recurrence: x_R' = b^2 - a^2 + embed(T.x)  (x bound constant) ===")
nativePrime=21888242871839275222246405745257275088548364400416034343698204186575808495617
def run(N, reset_every=None):
    xlo,xhi=[0]*8,dcap[:]; ylo,yhi=[0]*8,dcap[:]; out=[]; total=0
    for d in range(N):
        # rel1: a*(embed(Tx)-x_R) - Ty + y_R
        d1lo=[-xhi[i] for i in range(8)]; d1hi=[dcap[i]-xlo[i] for i in range(8)]
        p1lo,p1hi=prod_bounds(alo,ahi,d1lo,d1hi); r1lo=add(p1lo,ylo); r1hi=add(p1hi,yhi)
        L1=rel_layout(r1lo,r1hi); L1=(L1[0]-(R-1),L1[1],L1[2]-(R-1),L1[3]); k1,q1,t1,tb1=cert_params(*L1)
        # x_S = a^2 - x_R - embed(Tx)
        xSlo=[SLO[i]-xhi[i]-dcap[i] for i in range(8)]; xShi=[SHI[i]-xlo[i] for i in range(8)]
        # rel2: a*(x_R-x_S) + b*(x_R-x_S) - 2 y_R
        d2lo=sub(xlo,xShi); d2hi=sub(xhi,xSlo); pAlo,pAhi=prod_bounds(alo,ahi,d2lo,d2hi)
        r2lo=sub(add(pAlo,pAlo),scale(yhi,2)); r2hi=sub(add(pAhi,pAhi),scale(ylo,2))
        L2=rel_layout(r2lo,r2hi); k2,q2,t2,tb2=cert_params(*L2)
        # x_R' = b^2 - a^2 + embed(Tx)   -- CANCELLED FORM
        xlo2=[SLO[i]-SHI[i] for i in range(8)]; xhi2=[SHI[i]-SLO[i]+dcap[i] for i in range(8)]
        # y_R' = y_R + b*(x_S - x_R') - a*(x_R - x_S)
        d3lo=sub(xSlo,xhi2); d3hi=sub(xShi,xlo2); pClo,pChi=prod_bounds(alo,ahi,d3lo,d3hi)
        ylo2=add(add(ylo,pClo),neg(pAhi)); yhi2=add(add(yhi,pChi),neg(pAlo))
        # residual extrema (their admitted_extrema shape) — must be < nativePrime (we'll use 2^250)
        res=max(abs(L1[0]-(R-c)*(k1+2**q1-1)-R*(t1+2**tb1-1)), abs(L1[1]-(R-c)*k1-R*t1),
                abs(L2[0]-(R-c)*(k2+2**q2-1)-R*(t2+2**tb2-1)), abs(L2[1]-(R-c)*k2-R*t2))
        total+=(q1+tb1)+(q2+tb2)
        out.append((d,max(abs(v) for v in xlo2+xhi2).bit_length(),max(abs(v) for v in ylo2+yhi2).bit_length(),q1,tb1,q2,tb2,res.bit_length()))
        xlo,xhi,ylo,yhi=xlo2,xhi2,ylo2,yhi2
        if reset_every and (d+1)%reset_every==0:
            # canonicalise y only (x bound is constant anyway): cost 4 + 256/260 + cert
            rylo=[ylo[i]-dcap[i] for i in range(8)]; RY=rel_layout(rylo,yhi); ky,qy,ty,tby=cert_params(*RY)
            total+=4+258+qy+tby; ylo,yhi=[0]*8,dcap[:]
    return out,total
rows,tot=run(62)
print(" d | xbits ybits | rel1 q/t | rel2 q/t | resid bits (<250 ok)")
for r in rows[:6]+rows[6:62:8]+rows[-2:]: print(f"{r[0]:2d} |  {r[1]:3d}  {r[2]:3d}  |  {r[3]:3d}/{r[4]:3d} |  {r[5]:3d}/{r[6]:3d} |  {r[7]}")
print(f"NO RESETS over 62 steps: total cert rows = {tot}  ({tot/62:.1f}/step); max resid bits = {max(r[7] for r in rows)}")
for N in (10,15,20,31):
    _,t=run(62,N); print(f"reset y every {N}: total cert+reset rows = {t} ({t/62:.1f}/step)")
