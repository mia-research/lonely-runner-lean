B=7
def diag(p, readout, deg, a):
    Fp=GF(p); E=EllipticCurve(Fp,[0,B]); n=E.order()
    G=None
    for P in E.points():
        if P.order()==n: G=P;break
    dlog={};Q=E(0)
    for d in range(n): dlog[Q]=d;Q=Q+G
    zeta=CDF(exp(2*CDF(pi)*CDF(I)/n))
    pk=[]
    for k in range(1,deg+1):
        Fk=GF(p**k,'g');Ek=EllipticCurve(Fk,[0,B]);frob=Fk.frobenius_endomorphism()
        S=CDF(0)
        for P in Ek.points():
            if P.is_zero():continue
            v = P[1] if readout=='y' else P[0]
            if v==0:continue
            c=1 if v.is_square() else -1
            T=Ek(0);Pi=P
            for i in range(k): T=T+Pi;Pi=Ek(frob(Pi[0]),frob(Pi[1]))
            dl=0 if T.is_zero() else dlog[E(Fp(T[0]),Fp(T[1]))]
            S+=c*zeta**(a*dl)
        pk.append(-S)
    e=[1]
    for k in range(1,deg+1):
        s=0
        for i in range(1,k+1): s+=(-1)**(i-1)*e[k-i]*pk[i-1]
        e.append(s/k)
    R.<t>=CDF[]; poly=sum((-1)**j*e[j]*t**(deg-j) for j in range(deg+1))
    roots=[r for r,_ in poly.roots()]
    print("  %s deg=%d a=%d: |V|/sqrtp=%.3f  e_deg/p^(deg/2)=%.3f  mods=%s"
          %(readout,deg,a,abs(pk[0])/sqrt(p),abs(e[deg])/p**(deg/2.0),[round(abs(r)/sqrt(p),3) for r in roots]))

# p=67 chi2(x): try deg 2,3,4
diag(67,'x',2,11); diag(67,'x',3,11); diag(67,'x',4,11)
print("---")
diag(67,'y',4,17); diag(67,'y',2,17)
