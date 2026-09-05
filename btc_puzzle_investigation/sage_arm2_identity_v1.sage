# TEST the 120-degree structure via the predicted power-sum identity  m1^2 + m2 = 2p
# where m_k = sum of k-th powers of the 4 twisted eigenvalues, m_k = -S_k,
# S_1 = sum_{E(F_p)} chi2(y) psi_a,  S_2 = sum_{E(F_p^2)} chi2(Nm y) psi_a(Tr).
# If m1^2+m2=2p for ALL a, then V_y(a)=m1=2 sqrt p cos(psi), |V|<=2 sqrt p. PROOF mechanism.
B=7
def test(p, amax=8):
    Fp=GF(p); E=EllipticCurve(Fp,[0,B]); n=E.order()
    if not is_prime(n): return None
    G=None
    for P in E.points():
        if P.order()==n: G=P;break
    dlog={};Q=E(0)
    for d in range(n): dlog[Q]=d;Q=Q+G
    zeta=CDF(exp(2*CDF(pi)*CDF(I)/n))
    # k=1 data
    d1=[]
    for P in E.points():
        if P.is_zero() or P[1]==0: continue
        c=1 if P[1].is_square() else -1
        d1.append((c,dlog[P]))
    # k=2 data
    F2=GF(p**2,'g'); E2=EllipticCurve(F2,[0,B]); frob=F2.frobenius_endomorphism()
    d2=[]
    for P in E2.points():
        if P.is_zero() or P[1]==0: continue
        # chi2 over F_p^2 = chi2(Norm to F_p) ; Norm(y)=y*y^p
        Ny=P[1]*frob(P[1])
        c=1 if Fp(Ny).is_square() else -1
        T=P+E2(frob(P[0]),frob(P[1]))   # Tr_2(P)=P+Frob(P) in E(F_p)
        dl=0 if T.is_zero() else dlog[E(Fp(T[0]),Fp(T[1]))]
        d2.append((c,dl))
    res=[]
    for a in range(1,min(amax,n)):
        S1=sum(c*zeta**(a*dl) for c,dl in d1)
        S2=sum(c*zeta**(a*dl) for c,dl in d2)
        m1=-S1; m2=-S2
        lhs=m1*m1+m2
        res.append((a, abs(m1)/sqrt(p), abs(lhs-2*p)))   # |m1|/sqrtp, |m1^2+m2-2p|
    return dict(p=p,n=n,res=res)
for p in [13,43,67,79,103,127,139,151,163]:
    if p%3!=1 or B%p==0: continue
    r=test(p,amax=7)
    if not r: continue
    worst=max(e for _,_,e in r['res'])
    maxV=max(v for _,v,_ in r['res'])
    print("p=%-4d n=%-4d  max|V|/sqrtp=%.3f  MAX|m1^2+m2-2p|=%.2e  %s"
          %(r['p'],r['n'],maxV,worst,"IDENTITY HOLDS" if worst<1e-6 else "FAILS"))
