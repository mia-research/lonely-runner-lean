# MATCHED NULL for the cheap-shadow candidate: is x-half/sign(xy) rho > shuffled-d rho? (exact +-1 data)
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
def rho(Fvals):  # Fvals array len n-1 (d=1..n-1); rho=max_a|FFT|/n / l2 -- ranked stat, matched null
    F=np.concatenate([[0.0],Fvals]).astype(complex)
    l2=math.sqrt(np.mean(np.abs(F[1:])**2)) or 1e-12
    C=np.abs(np.fft.fft(F))/len(F); C[0]=0
    return C.max()/l2
rng=np.random.default_rng(7)
for p,A,B in [(67,0,7),(163,0,7),(283,0,7)]:
    pts=[(x,y) for x in range(p) for y in range(p) if (y*y-x*x*x-A*x-B)%p==0]
    n=len(pts)+1
    if not isprime(n): continue
    G=pts[0];P=[None]*n;Q=None
    for d in range(1,n):Q=ec_add(Q,G,A,p);P[d]=Q
    for nm,f in [('x-half', lambda x,y:1.0 if x<p/2 else -1.0),('sign(xy)',lambda x,y:1.0 if (x*y%p)<p/2 else -1.0)]:
        Ftrue=np.array([f(P[d][0],P[d][1]) for d in range(1,n)])
        rt=rho(Ftrue)
        # matched null: shuffle which point sits at each d-position (permute the F multiset)
        ge=0;B_=800
        for _ in range(B_):
            rs=rho(rng.permutation(Ftrue))
            if rs>=rt: ge+=1
        pv=(ge+1)/(B_+1)
        print(f"p={p} n={n} {nm:9}: true rho={rt:.4f}  shuffle-null perm p={pv:.4f}  {'LEAK (true>>shuffled)' if pv<0.02 else 'null (within shuffle spread)'}")
