# Compute e1,e2,e3,e4 of L*(a,T) for chi2(y), via power sums S_k = -sum_{E(F_p^k)} chi2^k(y) psi_a(Tr_k P).
# Validate against forced e4=p^2, e3=chi2(-1)*p*e1.  Then find e2 = g(e1,p) that the 120-law imposes.
B=7
def cell_data(p, kmax=3, amax=None):
    Fp=GF(p); E=EllipticCurve(Fp,[0,B]); n=E.order()
    if not is_prime(n): return None
    G=None
    for P in E.points():
        if P.order()==n: G=P;break
    dlog={};Q=E(0)
    for d in range(n): dlog[Q]=d;Q=Q+G
    CF=ComplexField(80); zeta=CF(exp(2*CF(pi)*CF(I)/n))
    chi_m1 = 1 if Fp(-1).is_square() else -1
    perk=[]
    for k in range(1,kmax+1):
        Fk=GF(p**k,'g'); Ek=EllipticCurve(Fk,[0,B]); frob=Fk.frobenius_endomorphism()
        data=[]
        for P in Ek.points():
            if P.is_zero(): continue
            y=P[1]
            if y==0: continue
            c = 1 if y.is_square() else -1
            T=Ek(0); Pi=P
            for i in range(k): T=T+Pi; Pi=Ek(frob(Pi[0]),frob(Pi[1]))
            dl=0 if T.is_zero() else dlog[E(Fp(T[0]),Fp(T[1]))]
            data.append((c,dl))
        perk.append(data)
    out=[]
    amax = amax or n
    for a in range(1,amax):
        S=[ -sum(c*zeta**((k+1)*0+a*dl) for c,dl in perk[k]) if False else -sum(c*zeta**(a*dl) for c,dl in perk[0]) for k in range(0,1)]
        # compute S_k properly for k=1..kmax
        Sk=[]
        for k in range(1,kmax+1):
            Sk.append(-sum(c*zeta**((a* dl)) for c,dl in perk[k-1]))   # note: psi_a on Tr, char raised to k via base field
        # Newton -> e1,e2,e3
        e1=Sk[0]
        e2=(e1*Sk[0]-Sk[1])/2
        e3=(e2*Sk[0]-e1*Sk[1]+Sk[2])/3 if kmax>=3 else None
        out.append((a,e1,e2,e3))
    return dict(p=p,n=n,chi_m1=chi_m1,out=out)

for p in [43,67]:
    r=cell_data(p,kmax=3,amax=6)
    if not r: continue
    print("=== p=%d n=%d chi2(-1)=%d ==="%(r['p'],r['n'],r['chi_m1']))
    for a,e1,e2,e3 in r['out']:
        # forced check e3 = chi2(-1)*p*e1
        chk3 = abs(e3 - r['chi_m1']*p*e1)
        # candidate: e2 = e1^2 + c*p ; solve c=(e2-e1^2)/p
        c = (e2 - e1*e1)/p
        print("  a=%d  e1=%.3f%+.3fi  e2=%.3f%+.3fi  |e3-chi2(-1)p e1|=%.1e   (e2-e1^2)/p = %.4f%+.4fi"
              %(a, e1.real(),e1.imag(), e2.real(),e2.imag(), float(chk3), c.real(),c.imag()))

print("\n===== wider sweep: (e2 - e1^2)/p across primes and p mod 4 =====")
for p in [13,61,79,103,127,151,163,181,193,277,337]:
    if p%3!=1 or B%p==0: continue
    r=cell_data(p,kmax=2,amax=None)
    if not r: continue
    vals=set()
    allreal=True
    for a,e1,e2,e3 in r['out']:
        c=(e2-e1*e1)/p
        vals.add(round(float(c.real()),4))
        if abs(c.imag())>1e-6: allreal=False
    print("  p=%-4d n=%-4d p%%4=%d  (e2-e1^2)/p values=%s  imag~0:%s"%(p,r['n'],p%4,sorted(vals),allreal))
