p = 43; B = 7
Fp = GF(p)
K.<x> = FunctionField(Fp); R.<T> = K[]
L.<w> = K.extension(T^4 - (x^3 + B))
J = L.jacobian(model='hess'); G0 = J.group()
E = EllipticCurve(Fp, [0, B]); G = E.gens()[0]; nE = G.order()
beta = Fp(36); b2 = beta^2
finite=[pl for pl in L.places(1) if not pl.is_infinite_place()]
coord={(Fp(x.evaluate(pl)),Fp(w.evaluate(pl))):pl for pl in finite}
_c={}
def lift(P):
    if P.is_zero(): return None
    k=(P[0],P[1])
    if k in _c: return _c[k]
    xP,yP=Fp(P[0]),Fp(P[1])
    if not yP.is_square(): _c[k]=None; return None
    r=yP.sqrt(); a=coord.get((xP,r)); b=coord.get((xP,-r))
    _c[k]=None if (a is None or b is None) else G0.point(a.divisor()-b.divisor())
    return _c[k]
phi=lambda P:E(beta*P[0],P[1]); phi2=lambda P:E(b2*P[0],P[1])
def build_S(P):
    Q0,Q1,Q2=lift(P),lift(phi(P)),lift(phi2(P))
    if None in (Q0,Q1,Q2): return None,None
    return Q0+Integer(b2)*Q1+Integer(beta)*Q2, Q1+Integer(b2)*Q2+Integer(beta)*Q0

# find a base of order 1893 among the S's, build dlog table ONCE
rat=[d for d in range(1,nE) if Fp((d*G)[1]).is_square()]
cands=[build_S(d*G)[0] for d in rat]
cands=[S for S in cands if S is not None and S.order()==1893]
base=cands[0]
print("building dlog table (1893)...", flush=True)
tab={}; cur=base.parent()(0) if hasattr(base.parent(),'__call__') else None
# construct zero element
zero=base-base
cur=zero
for i in range(1893):
    tab[str(cur)]=i; cur=cur+base
print(f"table built, distinct={len(tab)}", flush=True)
def dlog(S):
    return tab.get(str(S),None)

print("\n=== M5: sigma(S)=[k]S ? ===", flush=True)
for d in rat[:5]:
    S,sS=build_S(d*G)
    e=dlog(S); ep=dlog(sS)
    if e is None or ep is None: print(f"  d={d}: not in <base>"); continue
    oS=S.order()
    # k*e ≡ ep mod 1893 ; solve for k mod oS
    g=gcd(e,1893)
    if ep % g !=0: print(f"  d={d}: sigma(S) NOT a multiple of S (e={e},ep={ep})"); continue
    k=(ep//g)*inverse_mod((e//g),1893//g)% (1893//g)
    print(f"  d={d}: e={e} ep={ep} ord(S)={oS} -> sigma(S)=[{k}]S ; k^3 mod {oS} = {Integer(k)^3%oS} ; k!=1: {k%oS!=1}", flush=True)

print("\n=== I1: does e=dlog(S([d]G)) track d? ===", flush=True)
for d in range(1,nE):
    S,_=build_S(d*G)
    if S is None: print(f"  d={d:2d}: no rational lift", flush=True); continue
    e=dlog(S)
    print(f"  d={d:2d}: dlog(S)={e}  ord(S)={S.order()}", flush=True)
