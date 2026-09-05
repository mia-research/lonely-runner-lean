# AUDIT 1: is the Doc-12 residual deficit (vs a SYMMETRY-MATCHED control) real, or ~0?
import numpy as np, math
from sympy import isprime, legendre_symbol
def curve(p,A,B):
    def add(P,Q):
        if P is None:return Q
        if Q is None:return P
        x1,y1=P;x2,y2=Q
        if x1==x2 and (y1+y2)%p==0:return None
        m=((3*x1*x1+A)*pow(2*y1,-1,p) if P==Q else (y2-y1)*pow((x2-x1)%p,-1,p))%p
        x3=(m*m-x1-x2)%p;return(x3,(m*(x1-x3)-y1)%p)
    pts=[None]+[(x,y) for x in range(p) for y in range(p) if (y*y-(x**3+A*x+B))%p==0]
    N=len(pts)
    if not isprime(N):return None
    G=None
    for Q in pts:
        if Q is None:continue
        R=Q;k=1
        while R is not None:R=add(R,Q);k+=1
        if k==N:G=Q;break
    orb=[];R=None
    for d in range(1,N):R=add(R,G);orb.append(R)
    return N,np.array([P[1] for P in orb])
def first_nonCM(p):
    for A in range(1,p):
        for B in range(1,p):
            if (4*A**3+27*B**2)%p==0:continue
            r=curve(p,A,B)
            if r is not None:return A,B,r
    return None
def meanmag_lowtail(ys,p,n,en):
    U=np.abs(np.exp(2j*math.pi*np.outer(np.arange(1,p),ys)/p)@en)
    return U.mean(), np.mean(U/math.sqrt(n-1)<0.5)
print("AUDIT: deficit & low-tail vs SYMMETRY-MATCHED control (keeps +/- antisymmetry, K=300)")
print("p    n    real|U|  matched|U|  defc%    z_defc   realLow  matchLow  z_low")
rng=np.random.default_rng(7)
for p in [43,67,103,163,199,283]:
    r=first_nonCM(p)
    if r is None: continue
    A,B,(n,ys)=r
    en=np.exp(-2j*math.pi*np.arange(1,n)/n)
    rm,rl=meanmag_lowtail(ys,p,n,en)
    half=(n-1)//2
    cm=[];cl=[]
    for _ in range(300):
        perm=rng.permutation(half)
        yp=np.empty(n-1,dtype=int)
        for k in range(half):
            yp[k]=ys[perm[k]]; yp[n-2-k]=(-ys[perm[k]])%p
        m,l=meanmag_lowtail(yp,p,n,en); cm.append(m); cl.append(l)
    cm=np.array(cm);cl=np.array(cl)
    defc=100*(rm-cm.mean())/cm.mean(); z=(rm-cm.mean())/cm.std()
    zl=(rl-cl.mean())/cl.std() if cl.std()>0 else 0
    print(f"{p:3d} {n:4d} {rm:8.4f} {cm.mean():9.4f} {defc:+7.2f} {z:+8.2f}  {100*rl:6.2f}  {100*cl.mean():7.2f} {zl:+7.2f}")
