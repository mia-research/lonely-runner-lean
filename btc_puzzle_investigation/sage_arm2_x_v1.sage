# chi2(x) sheaf is degree 2: only k=1,2 needed.  Show it reaches 2 eigenvalues aligning to 2 sqrt p.
B=7
def eig_x(p, amax=None):
    Fp=GF(p); E=EllipticCurve(Fp,[0,B]); n=E.order()
    if not is_prime(n): return None
    G=None
    for P in E.points():
        if P.order()==n: G=P;break
    dlog={};Q=E(0)
    for d in range(n): dlog[Q]=d;Q=Q+G
    zeta=CDF(exp(2*CDF(pi)*CDF(I)/n))
    perk=[]
    for k in (1,2):
        Fk=GF(p**k,'g');Ek=EllipticCurve(Fk,[0,B]);frob=Fk.frobenius_endomorphism()
        data=[]
        for P in Ek.points():
            if P.is_zero():continue
            x=P[0]
            if x==0:continue
            c=1 if x.is_square() else -1
            T=Ek(0);Pi=P
            for i in range(k): T=T+Pi;Pi=Ek(frob(Pi[0]),frob(Pi[1]))
            dl=0 if T.is_zero() else dlog[E(Fp(T[0]),Fp(T[1]))]
            data.append((c,dl))
        perk.append(data)
    best=0;besta=0;bestcfg=None
    amax=amax or n
    for a in range(1,amax):
        p1=-sum(c*zeta**(a*dl) for c,dl in perk[0])
        p2=-sum(c*zeta**(2*a*dl) for c,dl in perk[1])
        e1=p1; e2=(p1*p1-p2)/2
        R.<t>=CDF[]; poly=t^2-e1*t+e2
        roots=[r for r,_ in poly.roots()]
        v=abs(p1)/sqrt(p)
        if v>best: best=v;besta=a;bestcfg=(sorted([abs(r)/sqrt(p) for r in roots]),sorted([RDF(arg(r)/pi*180) for r in roots]))
    return dict(p=p,n=n,best=best,besta=besta,cfg=bestcfg)

for p in [43,67,79,103,127,139,151,163]:
    if p%3!=1 or B%p==0: continue
    r=eig_x(p)
    if r: print("p=%d n=%d  max|Vx|/sqrtp=%.3f at a=%d  eig mods=%s args=%s"
                %(r['p'],r['n'],r['best'],r['besta'],[round(m,3) for m in r['cfg'][0]],[round(x,1) for x in r['cfg'][1]]))
