exec(open('envelope.py').read().split("print(\"\\n=== VAR-BASE")[0])   # primitives (validated)
import json
nativePrime=21888242871839275222246405745257275088548364400416034343698204186575808495617
def rel_layout(vlo,vhi): return half(vlo,0),half(vhi,0),half(vlo,1),half(vhi,1)
def neg(v): return [-x for x in v]
def scale(v,s): return [s*x for x in v]
def sq_bounds(lo,hi): return prod_bounds(lo,hi,lo,hi)   # corner bound (sound, slightly loose on diagonal)
def elo(v): return [v[i] if i%2==0 else 0 for i in range(8)]
zero=[0]*8
# Embedded canonical T.x, T.y: words in [0, dcap]
Tlo, Thi = zero, dcap[:]
sqT = sq_bounds(Tlo,Thi)
def resid(L,k,qb,t,tb):
    return max(abs(L[0]-(R-c)*(k+2**qb-1)-R*(t+2**tb-1)), abs(L[1]-(R-c)*k-R*t),
               abs(L[2]-(R-1)*(k+2**qb-1)+t), abs(L[3]-(R-1)*k+(t+2**tb-1)))

def run(N=62, verbose=True):
    # acc state: x in [xlo,xhi], y in [ylo,yhi]; seed = embedded canonical point
    xlo,xhi=zero[:],dcap[:]; ylo,yhi=zero[:],dcap[:]
    rows=[]; total=0; worst={}
    for d in range(N):
        # --- tangent cert: a*(2 yR) - 3 xR^2  (mod q) ---
        pTlo,pThi=prod_bounds(alo,ahi,scale(ylo,2),scale(yhi,2))
        sx=sq_bounds(xlo,xhi)
        r1lo=sub(pTlo,scale(sx[1],3)); r1hi=sub(pThi,scale(sx[0],3))
        L1=rel_layout(r1lo,r1hi); k1,q1,t1,tb1=cert_params(*L1)
        # --- x2 = a^2 - 2 xR ; y2 = a*(xR - x2) - yR ---
        x2lo=[SLO[i]-2*xhi[i] for i in range(8)]; x2hi=[SHI[i]-2*xlo[i] for i in range(8)]
        p2lo,p2hi=prod_bounds(alo,ahi,sub(xlo,x2hi),sub(xhi,x2lo))
        y2lo=sub(p2lo,yhi); y2hi=sub(p2hi,ylo)
        # --- x-equality cert (conditional): x2 - embed(Tx) ---
        e_lo=sub(x2lo,Thi); e_hi=sub(x2hi,Tlo)
        # halves also include the z=0 case (all zero) -> min with 0
        LX=rel_layout(e_lo,e_hi); LX=(min(LX[0],0),max(LX[1],0),min(LX[2],0),max(LX[3],0))
        kx,qx,tx,tbx=cert_params(*LX)
        # --- unified add cert: b*(y2 + Ty) - (x2^2 + x2*Tx + Tx^2)   OR (z=1) (y2 + Ty) ---
        slo=add(y2lo,Tlo); shi=add(y2hi,Thi)
        pUlo,pUhi=prod_bounds(alo,ahi,slo,shi)
        sx2=sq_bounds(x2lo,x2hi); px2T=prod_bounds(x2lo,x2hi,Tlo,Thi)
        rhs_lo=add(add(sx2[0],px2T[0]),sqT[0]); rhs_hi=add(add(sx2[1],px2T[1]),sqT[1])
        u_lo=sub(pUlo,rhs_hi); u_hi=sub(pUhi,rhs_lo)
        # union with the z=1 branch (y2+Ty) bounds
        u_lo=[min(u_lo[i],slo[i]) for i in range(8)]; u_hi=[max(u_hi[i],shi[i]) for i in range(8)]
        LU=rel_layout(u_lo,u_hi); ku,qu,tu,tbu=cert_params(*LU)
        # --- x' = b^2 - x2 - Tx ; y' = b*(x2 - x') - y2 ---
        xlo2=[SLO[i]-x2hi[i]-Thi[i] for i in range(8)]; xhi2=[SHI[i]-x2lo[i]-Tlo[i] for i in range(8)]
        p3lo,p3hi=prod_bounds(alo,ahi,sub(x2lo,xhi2),sub(x2hi,xlo2))
        ylo2=sub(p3lo,y2hi); yhi2=sub(p3hi,y2lo)
        # output mux: acc' in {x', x2, Tx, 0} -> envelope = union
        xlo2=[min(xlo2[i],x2lo[i],0) for i in range(8)]; xhi2=[max(xhi2[i],x2hi[i],Thi[i]) for i in range(8)]
        ylo2=[min(ylo2[i],y2lo[i],0) for i in range(8)]; yhi2=[max(yhi2[i],y2hi[i],Thi[i]) for i in range(8)]
        rs=max(resid(L1,k1,q1,t1,tb1),resid(LX,kx,qx,tx,tbx),resid(LU,ku,qu,tu,tbu))
        total+=(q1+tb1)+(qx+tbx)+(qu+tbu)
        rows.append(dict(d=d,xbits=max(abs(v) for v in xlo2+xhi2).bit_length(),ybits=max(abs(v) for v in ylo2+yhi2).bit_length(),
                         q1=q1,t1=tb1,qx=qx,tx=tbx,qu=qu,tu=tbu,resid=rs.bit_length(),
                         L1=L1,k1=k1,t1min=t1,LX=LX,kx=kx,txmin=tx,LU=LU,ku=ku,tumin=tu))
        xlo,xhi,ylo,yhi=xlo2,xhi2,ylo2,yhi2
    return rows,total,(xlo,xhi,ylo,yhi)

rows,tot,final=run(62)
print(" d | xbits ybits | tan q/t | xeq q/t | add q/t | resid")
for r in rows[:4]+rows[4:62:10]+rows[-2:]:
    print(f"{r['d']:2d} |  {r['xbits']:3d}  {r['ybits']:3d}  | {r['q1']:3d}/{r['t1']:3d} | {r['qx']:3d}/{r['tx']:3d} | {r['qu']:3d}/{r['tu']:3d} | {r['resid']}")
print(f"per-depth cert bits over 62 steps: {tot} ({tot/62:.1f}/step);  cost units ~ {2*tot}")
# single steady layout = union over all depths (constant circuit)
def union(key):
    Ls=[r[key] for r in rows]; return (min(l[0] for l in Ls),max(l[1] for l in Ls),min(l[2] for l in Ls),max(l[3] for l in Ls))
lay={}
for name,key in (('tan','L1'),('xeq','LX'),('add','LU')):
    L=union(key); k,qb,t,tb=cert_params(*L); lay[name]=dict(loMin=L[0],loMax=L[1],hiMin=L[2],hiMax=L[3],kmin=k,qbits=qb,tmin=t,tbits=tb)
    print(f"steady {name}: q/t = {qb}/{tb}  resid bits {resid(L,k,qb,t,tb).bit_length()}")
st=sum(lay[n]['qbits']+lay[n]['tbits'] for n in lay)
print(f"steady per step cert bits = {st}, cost units ~{2*st}; over 62: {62*st} (vs per-depth {tot})")
json.dump(dict(layouts=lay,final=[[int(v) for v in vec] for vec in final]),open('dta.json','w'))
