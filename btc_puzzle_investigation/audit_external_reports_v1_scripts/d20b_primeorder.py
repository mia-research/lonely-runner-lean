import numpy as np, math
from sympy import isprime, legendre_symbol, primerange
def orbit_ys(p,A,B):
    def add(P,Q):
        if P is None:return Q
        if Q is None:return P
        x1,y1=P;x2,y2=Q
        if x1==x2 and (y1+y2)%p==0:return None
        if P==Q:m=(3*x1*x1+A)*pow(2*y1,-1,p)%p
        else:m=(y2-y1)*pow((x2-x1)%p,-1,p)%p
        x3=(m*m-x1-x2)%p;y3=(m*(x1-x3)-y1)%p;return(x3,y3)
    pts=[None]+[(x,y) for x in range(p) for y in range(p) if (y*y-(x**3+A*x+B))%p==0]
    N=len(pts)
    if not isprime(N): return None
    G=None
    for Q in pts:
        if Q is None:continue
        R=Q;k=1
        while R is not None:R=add(R,Q);k+=1
        if k==N:G=Q;break
    orb=[];R=None
    for d in range(1,N):R=add(R,G);orb.append(R)
    return N,[P[1] for P in orb]
def maxratio(p,A,B):
    r=orbit_ys(p,A,B)
    if r is None: return None
    n,ys=r
    ch=np.array([0 if int(y)%p==0 else int(legendre_symbol(int(y)%p,p)) for y in ys])
    d=np.arange(1,n); M=0
    for a in range(1,n):
        V=abs(np.sum(ch*np.exp(2j*math.pi*a*d/n)))
        if V>M:M=V
    return M/math.sqrt(p)
print("=== PRIME-ORDER non-CM curves only: max |V|/sqrt(p) ===")
glob=0;where=None;count_over=0;total=0
for p in [pp for pp in primerange(13,180) if pp%4==1]:
    pm=0
    for A in range(1,min(p,14)):
        for B in range(1,min(p,14)):
            if (4*A**3+27*B**2)%p==0: continue
            r=maxratio(p,A,B)
            if r is None: continue
            total+=1
            if r>=2: count_over+=1
            if r>pm:pm=r
            if r>glob:glob=r;where=(p,A,B)
    print(f"  p={p:3d}: max ratio (prime-order curves) = {pm:.4f}  {'*** >2' if pm>=2 else ''}")
print(f"\nGLOBAL max = {glob:.4f} at {where}; prime-order curves with ratio>=2: {count_over}/{total}")
