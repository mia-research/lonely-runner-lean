from sage.schemes.cyclic_covers.constructor import CyclicCover

# CLAIM B: N_a (the *new* deg-4 part) takes "exactly two shapes". And: decompose the
# 6 full-signature classes into E_a (elliptic, deg2) vs N_a (new, deg4) contributions.
def parts(p, a):
    F=GF(p); R=PolynomialRing(F,'x'); x=R.gen()
    Lf=CyclicCover(4, x^3+F(a)).frobenius_polynomial().change_ring(ZZ)
    E=EllipticCurve(GF(p),[0,a]); ap=E.trace_of_frobenius()
    T=Lf.parent().gen(); Ef=T^2-ap*T+p
    q,r=Lf.quo_rem(Ef)
    return tuple(ZZ(c) for c in Ef.list()), tuple(ZZ(c) for c in q.list()), (r==0)

for p in [43,67,127,163,691]:
    Efset=set(); Nset=set(); Lset=set(); bad=0
    for a in range(1,p):
        ef,nf,exact=parts(p,a)
        if not exact: bad+=1; continue
        Efset.add(ef); Nset.add(nf); Lset.add((ef,nf))
    print("p=%4d | distinct E_a:%2d | distinct N_a:%2d | distinct full L_a:%2d | nonexact:%d"
          %(p,len(Efset),len(Nset),len(Lset),bad))
    print("        N_a shapes:", sorted(Nset))

# CLAIM C: eigenvalues of class-B N_a = sqrt(p) * WHICH roots of unity?
print("\n--- root system of N_a shapes (p=43) ---")
F=GF(43);R=PolynomialRing(F,'x');x=R.gen()
seen=set()
for a in range(1,43):
    Lf=CyclicCover(4,x^3+F(a)).frobenius_polynomial().change_ring(ZZ)
    E=EllipticCurve(GF(43),[0,a]);ap=E.trace_of_frobenius()
    T=Lf.parent().gen();q,_=Lf.quo_rem(T^2-ap*T+p)
    key=tuple(ZZ(c) for c in q.list())
    if key in seen: continue
    seen.add(key)
    # roots / sqrt(p): is s a root of unity? report its order
    for z in q.roots(QQbar,multiplicities=False):
        s=z/QQbar(43).sqrt()
        # multiplicative order of s if root of unity
        try: o=s.multiplicative_order()
        except Exception: o='not-root-of-unity'
        print("  N_a=%s  root/sqrt(p) order = %s"%(key,o))
        break
