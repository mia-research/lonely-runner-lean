# Arm 2: twisted Frobenius eigenvalue multiset of the chi2(y) sheaf (deg 4) and chi2(x) (deg 2).
# S_k(a) = sum_{P in E(F_p^k), P!=O} chi2^(p^k)(y_P) * psi_a(Tr_k(P)),  Tr_k = norm to E(F_p).
# For a!=0: S_k = -sum_i alpha_i^k.  Newton -> char poly; check |alpha_i|=sqrt(p).
B = 7
def eig_config(p, readout='y', deg=4, amax=6):
    Fp = GF(p); E = EllipticCurve(Fp,[0,B]); n = E.order()
    if not is_prime(n): return None
    # generator + dlog table on E(F_p)
    G=None
    for P in E.points():
        if P.order()==n: G=P; break
    dlog={}; Q=E(0)
    for d in range(n):
        dlog[Q]=d; Q=Q+G
    zeta = CDF(exp(2*CDF(pi)*CDF(I)/n))
    def psi(a, Q):    # e_n(a * dlog(Q))
        return zeta**(a*dlog[Q])
    res={}
    for a in range(1, min(amax, n)):
        pk=[]  # power sums -S_k
        ok=True
        for k in range(1, deg+1):
            Fk = GF(p**k, 'g'); Ek = EllipticCurve(Fk,[0,B])
            frob = Fk.frobenius_endomorphism()  # x->x^p
            S=CDF(0)
            for P in Ek.points():
                if P.is_zero(): continue
                y=P[1]
                if y==0: c=0
                else: c = 1 if y.is_square() else -1
                if c==0: continue
                # trace to E(F_p): P + frob(P) + ... + frob^{k-1}(P)
                T=Ek(0); Pi=P
                for i in range(k):
                    T = T + Pi
                    Pi = Ek(frob(Pi[0]), frob(Pi[1]))
                # T should be in E(F_p): coerce
                Tp = E(Fp(T[0]), Fp(T[1]))
                S += c * psi(a, Tp)
            pk.append(-S)  # power sum p_k = -S_k
        # Newton's identities -> elementary symmetric e_1..e_deg
        e=[1]
        for k in range(1, deg+1):
            s=0
            for i in range(1,k+1):
                s += (-1)**(i-1)*e[k-i]*pk[i-1]
            e.append(s/k)
        # char poly T^deg - e1 T^{deg-1} + e2 ... 
        R.<t>=CDF[]
        poly = sum((-1)**j * e[j]*t**(deg-j) for j in range(deg+1))
        roots=[r for r,_ in poly.roots()]
        mods=sorted([abs(r)/sqrt(p) for r in roots])
        args=sorted([ (arg(r)/pi*180) for r in roots])
        res[a]=(mods, args, [-pk_i for pk_i in [pk[0]]][0])  # V(a)=S_1=-pk0? 
    return dict(p=p,n=n,res=res)

for p in [13, 43]:
    r=eig_config(p, 'y', deg=4, amax=5)
    if not r: 
        print("p=%d skipped"%p); continue
    print("=== p=%d n=%d  chi2(y) deg-4 twisted eigenvalues ==="%(r['p'],r['n']))
    for a,(mods,args,V1) in r['res'].items():
        print("  a=%d  |alpha|/sqrtp=%s  args(deg)=%s"%(a,[round(m,3) for m in mods],[round(x,1) for x in args]))
