from sage.schemes.cyclic_covers.constructor import CyclicCover
for p in [43,163]:
    print("p=%d"%p)
    F=GF(p);R=PolynomialRing(F,'x');x=R.gen()
    seen=set()
    for a in range(1,p):
        Lf=CyclicCover(4,x^3+F(a)).frobenius_polynomial().change_ring(ZZ)
        E=EllipticCurve(GF(p),[0,a]);ap=E.trace_of_frobenius()
        T=Lf.parent().gen();q,_=Lf.quo_rem(T^2-ap*T+p)
        key=tuple(ZZ(c) for c in q.list())
        if key in seen:continue
        seen.add(key)
        orders=[]
        for z in q.roots(QQbar,multiplicities=False):
            s=z/QQbar(p).sqrt()
            try:orders.append(s.multiplicative_order())
            except:orders.append('inf')
        print("  N_a=%s  root/sqrt(p) orders=%s"%(q,sorted(orders)))
