# Confirm: chi2(x) new part dim 1 (2 eigenvalues); chi2(y) new part dim 2 (4 eigenvalues, CM).
# Roots of A_new char poly T^4 + m p T^2 + p^2 (m=1) -> arguments.
B=7
QT.<T>=QQ[]
def count_aff(Fq):
    from collections import Counter
    c4=Counter()
    for w in Fq: c4[w**4]+=1
    return sum(c4[x**3+B] for x in Fq)
for p in [43,67,79,103]:
    Fp=GF(p); aE=p+1-EllipticCurve(Fp,[0,B]).order(); LE=1-aE*T+p*T^2
    # chi2(x) new part (genus-2 cover)
    Hx=HyperellipticCurve(PolynomialRing(Fp,'w').0^6+B)
    Lx=QT([Hx.frobenius_polynomial().reverse()[i] for i in range(5)])
    nx=(Lx//LE)
    # chi2(y) new part
    Ns=[count_aff(GF(p**k,'g'))+1 for k in (1,2,3)]
    s=[(p**k+1-Ns[k-1]) for k in (1,2,3)]
    e=[1]
    for k in range(1,4):
        acc=0
        for i in range(1,k+1): acc+=(-1)**(i-1)*e[k-i]*s[i-1]
        e.append(acc/k)
    Ly=QT([1,-e[1],e[2],-e[3],p*e[2],-p**2*e[1],p**3]); ny=Ly//LE
    # eigenvalue args of ny (reciprocal roots): ny(T)=prod(1-alpha T) -> alpha=1/root
    CC=ComplexField(40)
    rts=[1/r for r,_ in ny.change_ring(CC).roots()]
    args=sorted([round(float(r.argument()/pi*180),1) for r in rts])
    mods=[round(float(abs(r)/sqrt(p)),3) for r in rts]
    print("p=%-3d  chi2(x) new deg=%d (dim %d, 2 eig)  |  chi2(y) new deg=%d (dim %d, 4 eig)  A_new eig |a|/sqrtp=%s args=%s"
          %(p, nx.degree(), nx.degree()//2, ny.degree(), ny.degree()//2, mods, args))
