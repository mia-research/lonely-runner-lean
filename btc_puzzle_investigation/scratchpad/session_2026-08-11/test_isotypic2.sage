def corr(a,b):
    na=len(a)
    if na<2: return float('nan')
    ma=sum(a)/na; mb=sum(b)/na
    num=sum((x-ma)*(y-mb) for x,y in zip(a,b))
    da=sqrt(sum((x-ma)^2 for x in a)); db=sqrt(sum((y-mb)^2 for y in b))
    return float(num/(da*db)) if da>0 and db>0 else float('nan')

def analyze(p, Bc=7):
    Fp=GF(p); E=EllipticCurve(Fp,[0,Bc]); G=E.gens()[0]; n=G.order()
    if not is_prime(n): print(f"p={p}: n={n} not prime, skip"); return
    beta=[Fp(b) for b in range(2,p) if Fp(b)^3==1 and Fp(b)!=1][0]; b2=beta*beta
    phiG=E(beta*G[0],G[1]); lam=[k for k in range(1,n) if k*G==phiG][0]
    om=CDF(exp(2*pi*I/3))
    def chi3(xv):
        t=Fp(xv)^((p-1)//3); return {Fp(1):CDF(1), beta:om, b2:om*om}[t]
    def orbit6(d):
        s=set()
        for k in range(3):
            v=(pow(lam,k,n)*d)%n; s.add(v); s.add((n-v)%n)
        return s
    dat={}
    for d in range(1,n):
        P=d*G; xv=Fp(P[0]); yv=ZZ(P[1])
        t=float(chi3(xv).real())*float(yv)
        d0=min(orbit6(d))
        found=None
        for s in [0,1]:
            for j in range(3):
                if ((-1)^s * d0 * pow(lam,j,n))%n==d%n: found=(s,j); break
            if found: break
        s,j=found; c=((-1)^s * d0 * pow(lam,j,n) - d)//n
        dat[d]=(float(c),t,s,j,d0)
    cs=[dat[d][0] for d in range(1,n)]; ts=[dat[d][1] for d in range(1,n)]
    print(f"p={p} n={n} lam={lam}: GLOBAL Corr(c,t)={corr(cs,ts):.6f}")
    orbs={}
    for d in range(1,n): orbs.setdefault(dat[d][4],[]).append(d)
    print("  per-orbit Corr(c,t) (first 5):")
    for d0 in sorted(orbs)[:5]:
        ds=orbs[d0]; print(f"    d0={d0} (n={len(ds)}): {corr([dat[d][0] for d in ds],[dat[d][1] for d in ds]):.6f}")
    print("  ARTIFACT TEST: Corr(c,t) within FIXED s=0 (breaks shared-s cause):")
    for d0 in sorted(orbs)[:5]:
        ds=[d for d in orbs[d0] if dat[d][2]==0]
        print(f"    d0={d0} (s=0 pts {len(ds)}): {corr([dat[d][0] for d in ds],[dat[d][1] for d in ds])}")
    print("  §2.3 'is t constant within s-branch?' orbit d0=1:")
    for s in [0,1]:
        print(f"    s={s}: t={[round(dat[d][1],2) for d in orbs[min(orbs)] if dat[d][2]==s]}  c={[dat[d][0] for d in orbs[min(orbs)] if dat[d][2]==s]}")

analyze(163); print(); analyze(43)
