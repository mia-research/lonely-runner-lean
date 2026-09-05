import sys
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core
def gal(D, K, z, m):
    for t in (Integer(g) for g in Zmod(m).unit_gens()):
        if not (K.hom([z**t])(D)/D).is_square():
            return False, t
    return True, None
def build_L(p,a,K,z,n):
    dl=core.dlog_table(p,n); h1=core.hist_k1(p,n,dl); h2=core.hist_k2(p,n,dl)
    V1=sum(h1[d]*z**((a*d)%n) for d in range(n)); V2=sum(h2[d]*z**((a*d)%n) for d in range(n))
    leg=1 if p%4==1 else -1
    e1=-V1; e2=(V1**2+V2)/2; e3=leg*p*e1; e4=K(p**2)
    R=PolynomialRing(K,'T'); T=R.gen()
    return T**4-e1*T**3+e2*T**2-e3*T+e4
for p in (13,43):
    n=core.curve_order(p); m=12*n
    K=CyclotomicField(m); z=K.gen()
    a1,_=gal(K(5),K,z,m); a2,_=gal(z+2,K,z,m)
    print(f"p={p} m={m}: PLANT D=5 galois={a1}(want T)  PLANT D=z+2 galois={a2}(want F)", flush=True)
    Kn=CyclotomicField(n); zn=Kn.gen(); L=build_L(p,1,Kn,zn,n)
    phi=Kn.hom([z**12],K); R=PolynomialRing(K,'T'); T=R.gen()
    Lb=sum(phi(c)*T**i for i,c in enumerate(L.list()))
    facs=[f for f,e in Lb.factor()]
    for i,q in enumerate(facs):
        D=q[1]**2-4*q[0]
        if D.is_square(): print(f"  p={p} quad{i}: D square (splits)", flush=True); continue
        g_ok,t=gal(D,K,z,m)
        print(f"  p={p} quad{i}: galois(sigma(D)/D in K^2)={g_ok}" + ("" if g_ok else f" FAILS@sigma_{t} -> NON-ABELIAN"), flush=True)
