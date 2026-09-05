# Is the x-half "leak" just the forced x-even symmetry x_{P_d}=x_{P_{n-d}}? Control = EVEN-PRESERVING null.
import numpy as np, math
def egcd(a,b):
    if b==0:return(a,1,0)
    g,x,y=egcd(b,a%b);return(g,y,x-(a//b)*y)
def inv(a,m):return egcd(a%m,m)[1]%m
def ec_add(P,Q,a,p):
    if P is None:return Q
    if Q is None:return P
    (x1,y1),(x2,y2)=P,Q
    if x1==x2 and (y1+y2)%p==0:return None
    l=((3*x1*x1+a)*inv(2*y1,p) if P==Q else (y2-y1)*inv((x2-x1)%p,p))%p
    x3=(l*l-x1-x2)%p;return(x3,(l*(x1-x3)-y1)%p)
def isprime(m):
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return m>=2
def rho(Fvals):
    F=np.concatenate([[0.0],Fvals]).astype(complex)
    l2=math.sqrt(np.mean(np.abs(F[1:])**2)) or 1e-12
    C=np.abs(np.fft.fft(F))/len(F); C[0]=0
    return C.max()/l2
rng=np.random.default_rng(11)
for p in [67,163]:
    A,B=0,7
    pts=[(x,y) for x in range(p) for y in range(p) if (y*y-x*x*x-A*x-B)%p==0]
    n=len(pts)+1
    if not isprime(n): continue
    G=pts[0];P=[None]*n;Q=None
    for d in range(1,n):Q=ec_add(Q,G,A,p);P[d]=Q
    # verify x-even: x_{P_d}==x_{P_{n-d}}
    even_ok=all(P[d][0]==P[n-d][0] for d in range(1,n))
    Ftrue=np.array([1.0 if P[d][0]<p/2 else -1.0 for d in range(1,n)])   # x-half, indexed d=1..n-1
    rt=rho(Ftrue)
    half=(n-1)//2
    pairvals=[Ftrue[d-1] for d in range(1,half+1)]   # value on pair {d,n-d}, d=1..half
    ge=0;B_=800
    for _ in range(B_):
        pv=rng.permutation(pairvals)
        Fs=np.zeros(n-1)
        for i,d in enumerate(range(1,half+1)):
            Fs[d-1]=pv[i]; Fs[(n-d)-1]=pv[i]   # even-preserving
        if rho(Fs)>=rt: ge+=1
    pval=(ge+1)/(B_+1)
    print(f"p={p} n={n}: x-even forced? {even_ok} | true rho={rt:.4f}  EVEN-preserving-null perm p={pval:.4f}  -> {'STILL a leak beyond evenness' if pval<0.02 else 'explained by forced x-even symmetry (NOT a cheap leak)'}")
