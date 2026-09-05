from math import gcd
from collections import Counter
def egcd(a,b):
    if b==0: return (a,1,0)
    g,x,y=egcd(b,a%b); return (g,y,x-(a//b)*y)
def inv(a,m): return egcd(a%m,m)[1]%m
def ec_add(P,Q,a,p):
    if P is None: return Q
    if Q is None: return P
    (x1,y1),(x2,y2)=P,Q
    if x1==x2 and (y1+y2)%p==0: return None
    l=((3*x1*x1+a)*inv(2*y1,p) if P==Q else (y2-y1)*inv((x2-x1)%p,p))%p
    x3=(l*l-x1-x2)%p; return (x3,(l*(x1-x3)-y1)%p)
def lcm(a,b): return a*b//gcd(a,b)
def setup(p,A,B):
    pts=[(x,y) for x in range(p) for y in range(p) if (y*y-x*x*x-A*x-B)%p==0]
    N=len(pts)+1
    G=pts[0]
    P=[None]*N; Q=None
    for d in range(1,N):
        Q=ec_add(Q,G,A,p); P[d]=Q
    return N,P
def Tvec(a,b,p,n,P,M):
    f=Counter(); Mp,Mn=M//p,M//n
    for d in range(1,n):
        f[(Mp*b*P[d][0]-Mn*a*d)%M]+=1
    return f
def autocorr(f,M):
    g=Counter(); it=list(f.items())
    for j,cj in it:
        for i,ci in it: g[(j-i)%M]+=cj*ci
    return g

for p,(A,B) in [(43,(0,7)),(67,(0,7))]:
    n,P=setup(p,A,B); M=lcm(p,n)
    lam=next(t for t in range(2,n) if pow(t,3,n)==1 and t!=1)
    be=(P[lam][0]*inv(P[1][0],p))%p
    # sanity: x_{lam*d} == be * x_d  (the GLV/mu3 identity) -- EXACT integer check
    glv_pt = all(P[(lam*d)%n][0] == (be*P[d][0])%p for d in range(1,n))
    parity=True; glv=True; plancherel=True
    for b in range(1,p):
        for a in range(1,n):
            fab=Tvec(a,b,p,n,P,M)
            # parity (x-even): T(a,b) vs T(-a,b) magnitude (P_{n-d}=-P_d has same x)
            if autocorr(fab,M)!=autocorr(Tvec((-a)%n,b,p,n,P,M),M): parity=False
            # GLV/mu3 FULL equality: T(a,b) == T(a*lam, be*b)  (rigid phase, exact)
            if fab!=Tvec((a*lam)%n,(be*b)%p,p,n,P,M): glv=False
        if not(parity and glv): break
    # Plancherel: sum_a |T(a,b)|^2 == n*(n-1) exactly (each |c_d|=1). Verify via autocorr sum.
    for b in range(1,min(p,6)):
        tot=Counter()
        for a in range(n):
            for k,v in autocorr(Tvec(a,b,p,n,P,M),M).items(): tot[k]+=v
        # sum_a|T|^2 = tot[0] + sum_{k>0} tot[k] zeta^k ; equals n(n-1) iff tot[k]==0 for k>0 and tot[0]==n(n-1)
        val_ok = (tot[0]==n*(n-1)) and all(tot[k]==0 for k in tot if k!=0)
        plancherel = plancherel and val_ok
    print(f"p={p} n={n} lam={lam} beta={be}:  GLV-point-id x_(lam d)==be*x_d: {glv_pt} | EXACT parity |T(-a,b)|=|T(a,b)|: {parity} | GLV full-eq T(a,b)==T(a lam,be b): {glv} | Plancherel sum_a|T|^2==n(n-1): {plancherel}")
