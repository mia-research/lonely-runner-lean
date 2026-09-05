B = 7
def eig_config(p, deg=4, amax=6, verbose=True):
    Fp = GF(p); E = EllipticCurve(Fp,[0,B]); n = E.order()
    if not is_prime(n): return None
    G=None
    for P in E.points():
        if P.order()==n: G=P; break
    dlog={}; Q=E(0)
    for d in range(n): dlog[Q]=d; Q=Q+G
    zeta = CDF(exp(2*CDF(pi)*CDF(I)/n))
    # For each k, enumerate E(F_p^k) once: store (c_P, dlog(Tr_P)) for y-readout
    perk=[]
    for k in range(1, deg+1):
        Fk = GF(p**k,'g'); Ek = EllipticCurve(Fk,[0,B])
        frob = Fk.frobenius_endomorphism()
        data=[]
        for P in Ek.points():
            if P.is_zero(): continue
            y=P[1]
            if y==0: continue
            c = 1 if y.is_square() else -1
            T=Ek(0); Pi=P
            for i in range(k):
                T=T+Pi; Pi=Ek(frob(Pi[0]),frob(Pi[1]))
            if T.is_zero(): dl=0
            else: dl=dlog[E(Fp(T[0]),Fp(T[1]))]
            data.append((c,dl))
        perk.append(data)
    out={}
    for a in range(1,min(amax,n)):
        pk=[]
        for k in range(1,deg+1):
            S=sum(c*zeta**(a*dl) for (c,dl) in perk[k-1])
            pk.append(-S)     # power sum = -S_k
        e=[1]
        for k in range(1,deg+1):
            s=0
            for i in range(1,k+1): s+=(-1)**(i-1)*e[k-i]*pk[i-1]
            e.append(s/k)
        R.<t>=CDF[]
        poly=sum((-1)**j*e[j]*t**(deg-j) for j in range(deg+1))
        roots=[r for r,_ in poly.roots()]
        mods=sorted([abs(r)/sqrt(p) for r in roots])
        args=sorted([RDF(arg(r)/pi*180) for r in roots])
        V1=-pk[0]
        out[a]=(mods,args,abs(V1)/sqrt(p))
    return dict(p=p,n=n,out=out)

for p in [13,19,31]:
    if p%3!=1 or B%p==0: continue
    r=eig_config(p,deg=4,amax=6)
    if not r: print("p=%d n not prime, skip"%p); continue
    print("=== p=%d n=%d  chi2(y) deg-4 twisted eigenvalues (|alpha|/sqrtp, args in deg) ==="%(r['p'],r['n']))
    for a,(mods,args,v1) in r['out'].items():
        print("  a=%d |V|/sqrtp=%.3f | mods=%s args=%s"%(a,v1,[round(m,3) for m in mods],[round(x,1) for x in args]))
