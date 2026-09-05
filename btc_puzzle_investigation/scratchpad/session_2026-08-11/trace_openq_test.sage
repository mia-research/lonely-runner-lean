# Continue the OPEN isotypic-trace question with the OTHER ACCOUNTS' exact object:
# ell(d) = dlog_{A_new}( S([d]G) ),  S = isotypic projection.  Test Q1 (affine/GLV-halves), Q2 (orbit).
p = 43; B = 7
Fp = GF(p); K.<x> = FunctionField(Fp); R.<T> = K[]
L.<w> = K.extension(T^4 - (x^3 + B))
J = L.jacobian(model='hess'); G0 = J.group()
E = EllipticCurve(Fp, [0, B]); G = E.gens()[0]; nE = G.order()
beta = Fp(36); b2 = beta^2
# GLV lambda on E: phi(P)=[lam]P
lam=None
for cand in range(2,nE):
    if E(beta*G[0],G[1])==cand*G: lam=cand; break
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
    if None in (Q0,Q1,Q2): return None
    return Q0+Integer(b2)*Q1+Integer(beta)*Q2
rat=[d for d in range(1,nE) if Fp((d*G)[1]).is_square()]
cands=[build_S(d*G) for d in rat]; cands=[S for S in cands if S is not None and S.order()==1893]
base=cands[0]; zero=base-base
tab={}; cur=zero
for i in range(1893): tab[str(cur)]=i; cur=cur+base
def dlog(S): return tab.get(str(S),None)
ell={}
for d in range(1,nE):
    S=build_S(d*G)
    ell[d]=dlog(S) if S is not None else None
print("lambda=%d (lam^3 mod nE=%d), nE=%d, |A_new base|=1893"%(lam,(lam^3)%nE,nE))
print("ell(d)=dlog_Anew(S([d]G)):")
print({d:ell[d] for d in range(1,nE)})

# --- Q2: orbit covariance. is ell(lam*d mod nE) = k*ell(d) mod 1893 for fixed k? ---
print("\n[Q2] mu3-orbit covariance test: ell(lam d) vs ell(d)")
ks=set()
for d in range(1,nE):
    ld=(lam*d)%nE
    if ell[d] and ell.get(ld):
        e,el=ell[d],ell[ld]
        g=gcd(e,1893)
        if el%g==0:
            k=(el//g)*inverse_mod(e//g,1893//g)%(1893//g); ks.add(k)
print("   multipliers k s.t. ell(lam d)=k*ell(d):", sorted(ks), " (single value ⇒ clean covariance)")

# --- Q1: affine in d?  and does it factor through GLV halves (d1,d2)? ---
print("\n[Q1] affine test: is ell(d) = a*d+b mod 1893?  (3 pts determine a,b; check rest)")
pts=[(d,ell[d]) for d in range(1,nE) if ell[d] is not None]
(d1,e1),(d2,e2)=pts[0],pts[1]
try:
    a=((e2-e1)*inverse_mod((d2-d1)%1893,1893))%1893; bb=(e1-a*d1)%1893
    viol=sum(1 for (d,e) in pts if (a*d+bb)%1893!=e)
    print("   a=%d b=%d ; violations=%d/%d  (0 ⇒ AFFINE ⇒ lever; >0 ⇒ nonlinear)"%(a,bb,viol,len(pts)))
except Exception as ex: print("   (singular)",ex)

# --- structural: is the lift homomorphic? ell(2d)=2ell(d)? ---
print("\n[struct] homomorphism test ell(2d)=2 ell(d) mod 1893:")
h=[(d,ell[d],ell.get((2*d)%nE)) for d in range(1,nE//2) if ell[d] and ell.get((2*d)%nE)]
homok=sum(1 for d,e,e2 in h if (2*e)%1893==e2)
print("   holds %d/%d  (0/low ⇒ NON-homomorphic ⇒ no linear ECDLP transfer)"%(homok,len(h)))
