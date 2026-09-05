p = 43; B = 7
Fp = GF(p)
K.<x> = FunctionField(Fp)
R.<T> = K[]
L.<w> = K.extension(T^4 - (x^3 + B))
J = L.jacobian(model='hess'); G0 = J.group()
E = EllipticCurve(Fp, [0, B]); G = E.gens()[0]; nE = G.order()
beta = Fp(36); b2 = beta^2   # 36, 6
finite = [pl for pl in L.places(1) if not pl.is_infinite_place()]
coord = {}
for pl in finite:
    coord[(Fp(x.evaluate(pl)), Fp(w.evaluate(pl)))] = pl

def lift(P):
    if P.is_zero(): return None
    xP,yP = Fp(P[0]), Fp(P[1])
    if not yP.is_square(): return None
    r = yP.sqrt()
    a=coord.get((xP,r)); b=coord.get((xP,-r))
    if a is None or b is None: return None
    return G0.point(a.divisor()-b.divisor())

phi  = lambda P: E(beta*P[0], P[1])
phi2 = lambda P: E(b2*P[0],  P[1])

# --- M4 test: apply zeta3 to the DEGREE-1 input divisor of Q(P), compare to Q(phiP) ---
def lift_divisor(P):
    xP,yP=Fp(P[0]),Fp(P[1]); r=yP.sqrt()
    return coord[(xP,r)], coord[(xP,-r)]   # (plus_place, minus_place)
def zeta3_of_liftclass(P):
    # map (x,w)->(beta x, w) on the two degree-1 places, return class
    pl_plus, pl_minus = lift_divisor(P)
    xp,wp = Fp(x.evaluate(pl_plus)), Fp(w.evaluate(pl_plus))
    xm,wm = Fp(x.evaluate(pl_minus)), Fp(w.evaluate(pl_minus))
    np_plus = coord[(beta*xp, wp)]; np_minus = coord[(beta*xm, wm)]
    return G0.point(np_plus.divisor()-np_minus.divisor())

print(f"p={p} B={B}; |Jac|={G0.order()}=3*31*631; |E|={nE}; beta={beta}, beta^2={b2}")

print("\n=== M3: which d give F_43-rational lifts (y_[d]G a QR)? ===")
rat=[d for d in range(1,nE) if Fp((d*G)[1]).is_square()]
print(f"  rational-lift d: {len(rat)}/{nE-1}: {rat}")
if rat:
    print(f"  ord(Q([d]G)) for those d: {[lift(d*G).order() for d in rat[:8]]} ...")

print("\n=== M4: [zeta3]Q(P) == Q(phiP) ? ===")
ok=0;cnt=0
for d in rat:
    P=d*G
    if not Fp(phi(P)[1]).is_square(): continue
    if lift(phi(P)) is None: continue
    cnt+=1
    if zeta3_of_liftclass(P)==lift(phi(P)): ok+=1
print(f"  {ok}/{cnt} points satisfy [zeta3]Q(P)=Q(phiP)")

print("\n=== M5: S=Q0+beta^2 Q1+beta Q2; sigma(S) via reindex = Q1+beta^2 Q2+beta Q0; is sigma(S)=[k]S? ===")
def build_S(P):
    Q0,Q1,Q2 = lift(P),lift(phi(P)),lift(phi2(P))
    if None in (Q0,Q1,Q2): return None,None
    S      = Q0 + Integer(b2)*Q1 + Integer(beta)*Q2
    sigmaS = Q1 + Integer(b2)*Q2 + Integer(beta)*Q0
    return S,sigmaS
for d in rat:
    S,sS = build_S(d*G)
    if S is None: continue
    oS=S.order()
    ks=[k for k in range(oS) if k*S==sS]
    print(f"  d={d}: ord(S)={oS}; sigma(S)=[k]S for k in {ks}; is k a nontrivial cube root of 1 mod ord? {[ (Integer(k)^3 % oS, Integer(k)%oS!=1) for k in ks]}")
    if d==rat[0]: 
        # also report a few more
        pass

print("\n=== I1: d-recovery -- S([d]G) as multiple of a base, over the small Jacobian ===")
data=[]
for d in range(1,nE):
    P=d*G
    S,_=build_S(P)
    data.append((d,S))
present=[S for d,S in data if S is not None and S.order()>1]
if present:
    base=max(present,key=lambda s:s.order()); ob=base.order()
    print(f"  base order={ob}")
    for d,S in data:
        if S is None:
            print(f"    d={d:2d}: no rational lift"); continue
        e=[k for k in range(ob) if k*base==S]
        print(f"    d={d:2d}: S=[{e[0] if e else '?'}]*base  ord {S.order()}")
