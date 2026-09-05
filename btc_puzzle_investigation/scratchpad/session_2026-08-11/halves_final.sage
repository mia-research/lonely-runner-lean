p=43;B=7
Fp=GF(p); K.<x>=FunctionField(Fp); R.<T>=K[]
L.<w>=K.extension(T^4-(x^3+B))
J=L.jacobian(model='hess'); G0=J.group()
E=EllipticCurve(Fp,[0,B]); G=E.gens()[0]; nE=G.order()
beta=Fp(36); b2=beta^2
lam=[c for c in range(2,nE) if E(beta*G[0],G[1])==c*G][0]
finite=[pl for pl in L.places(1) if not pl.is_infinite_place()]
coord={(Fp(x.evaluate(pl)),Fp(w.evaluate(pl))):pl for pl in finite}
_c={}
def lift(P):
    if P.is_zero(): return None
    k=(P[0],P[1])
    if k in _c: return _c[k]
    xP,yP=Fp(P[0]),Fp(P[1])
    if not yP.is_square(): _c[k]=None; return None
    r=yP.sqrt(); a=coord.get((xP,r)); bb=coord.get((xP,-r))
    _c[k]=None if (a is None or bb is None) else G0.point(a.divisor()-bb.divisor())
    return _c[k]
phi=lambda P:E(beta*P[0],P[1]); phi2=lambda P:E(b2*P[0],P[1])
def build_S(P):
    Q0,Q1,Q2=lift(P),lift(phi(P)),lift(phi2(P))
    if None in (Q0,Q1,Q2): return None
    return Q0+Integer(b2)*Q1+Integer(beta)*Q2
rat=[d for d in range(1,nE) if Fp((d*G)[1]).is_square()]
cands=[S for S in (build_S(d*G) for d in rat) if S is not None]
base=[S for S in cands if S.order()==1893][0]
zero=base-base; tab={}; cur=zero
for i in range(1893): tab[str(cur)]=i; cur=cur+base
dlog=lambda S: tab.get(str(S),None)
def gauss(v1,v2):
    while True:
        if v1[0]^2+v1[1]^2>v2[0]^2+v2[1]^2: v1,v2=v2,v1
        m=round((v1[0]*v2[0]+v1[1]*v2[1])/(v1[0]^2+v1[1]^2))
        if m==0: return v1,v2
        v2=(v2[0]-m*v1[0],v2[1]-m*v1[1])
bb1,bb2=gauss((nE,0),((-lam)%nE,1)); Bm=matrix(ZZ,[list(bb1),list(bb2)]); Bi=Bm.inverse()
def halves(d):
    co=vector(QQ,[d,0])*Bi; rc=vector(ZZ,[round(co[0]),round(co[1])]); lp=rc*Bm
    return Integer(d-lp[0]),Integer(-lp[1])
data=[]
for d in range(1,nE):
    S=build_S(d*G)
    if S is None: continue
    e=dlog(S)
    if e is None: continue
    d1,d2=halves(d); data.append((d,d1,d2,e))
print("nE=%d lam=%d pts=%d  halves:"%(nE,lam,len(data)))
for r in data: print("  d=%2d (d1,d2)=(%3d,%3d) e=%4d"%r)
q=631; F=GF(q)
def fit(rows,feat):
    A=Matrix(F,[list(feat(r))+[1] for r in rows]); y=vector(F,[r[3]%q for r in rows])
    try:
        sol=A.solve_right(y)
        vv=sum(1 for r in rows if sum(sol[i]*feat(r)[i] for i in range(len(feat(r))))+sol[-1]!=F(r[3]%q))
        return vv,len(rows)
    except ValueError: return len(rows),len(rows)
import random; random.seed(int(1))
print("--- affine fits over GF(631) ---")
v,t=fit(data,lambda r:(r[0],));       print("affine-in-d        : %d/%d viol  [known NEG]"%(v,t))
v,t=fit(data,lambda r:(r[1],r[2]));   print("affine-in-(d1,d2)  : %d/%d viol  [THE TEST]"%(v,t))
synth=[(r[0],r[1],r[2],(7*r[1]+11*r[2]+5)%q) for r in data]
v,t=fit(synth,lambda r:(r[1],r[2]));  print("POSCTRL synth-affine: %d/%d viol  [expect 0]"%(v,t))
es=[r[3] for r in data]; random.shuffle(es); shuf=[(r[0],r[1],r[2],es[i]) for i,r in enumerate(data)]
v,t=fit(shuf,lambda r:(r[1],r[2]));   print("NEGCTRL shuffled-e  : %d/%d viol  [expect fail]"%(v,t))
