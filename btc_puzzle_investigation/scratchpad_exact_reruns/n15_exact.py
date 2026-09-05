# EXACT rerun of N15 joint-readout null: does any CHEAP predictor f(d) predict the joint readout
# T=(cubic-char(x_P), y-parity) beyond an exact permutation null? integer contingency, exact perm p.
from fractions import Fraction
from collections import Counter
import random
def egcd(a,b):
    if b==0: return(a,1,0)
    g,x,y=egcd(b,a%b);return(g,y,x-(a//b)*y)
def inv(a,m): return egcd(a%m,m)[1]%m
def ec_add(P,Q,a,p):
    if P is None: return Q
    if Q is None: return P
    (x1,y1),(x2,y2)=P,Q
    if x1==x2 and (y1+y2)%p==0: return None
    l=((3*x1*x1+a)*inv(2*y1,p) if P==Q else (y2-y1)*inv((x2-x1)%p,p))%p
    x3=(l*l-x1-x2)%p; return (x3,(l*(x1-x3)-y1)%p)
def isprime(m):
    if m<2:return False
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return True
def chi2stat(F,T):
    N=len(F);J=Counter(zip(F,T));mf=Counter(F);mt=Counter(T);chi=Fraction(0)
    for i in mf:
        for j in mt:
            nij=J.get((i,j),0);e=mf[i]*mt[j]
            if e: chi+=Fraction((nij*N-e)**2,e)
    return chi/N
def jac(a,n):
    a%=n;r=1
    while a:
        while a%2==0:
            a//=2
            if n%8 in(3,5):r=-r
        a,n=n,a
        if a%4==3 and n%4==3:r=-r
        a%=n
    return r%3 if n==1 else (r if n==1 else r)  # sign

for p,A,B in [(43,0,7),(67,0,7),(163,0,7)]:
    pts=[(x,y) for x in range(p) for y in range(p) if (y*y-x*x*x-A*x-B)%p==0]
    n=len(pts)+1
    if not isprime(n): 
        print(f"  p={p}: n={n} composite, skip"); continue
    G=pts[0];P=[None]*n;Q=None
    for d in range(1,n):Q=ec_add(Q,G,A,p);P[d]=Q
    # joint readout T=(cubic-char(x) in {0,1,2}, y-parity [2y>=p])
    T=[]; ds=list(range(1,n))
    for d in ds:
        x,y=P[d]; e=pow(x,(p-1)//3,p); elab={1:0}.get(e,None)
        if elab is None: elab=1 if e==pow(2,(p-1)//3,p) else 2  # 3-value label
        T.append((pow(x,(p-1)//3,p), 1 if 2*y>=p else 0))
    # cheap predictor family: singletons d%k, jacobi, cube-res(d,n); + all pairs
    def cres(d): return pow(d,(n-1)//3,n) if (n-1)%3==0 else 0
    singles={}
    for k in (3,6,7,9,12): singles[f"d%{k}"]=[d%k for d in ds]
    singles["jac(d,n)"]=[egcd(d%n,n)[0] and pow(d,(n-1)//2,n) for d in ds]
    if (n-1)%3==0: singles["cres(d,n)"]=[cres(d) for d in ds]
    feats=dict(singles)
    names=list(singles)
    for i in range(len(names)):
        for j in range(i+1,len(names)):
            feats[f"{names[i]}&{names[j]}"]=list(zip(singles[names[i]],singles[names[j]]))
    # exact max-stat over family + exact family-wise permutation p-value
    obs={f:chi2stat(feats[f],T) for f in feats}
    best=max(obs,key=lambda f:obs[f]); beststat=obs[best]
    rng=random.Random(7); Tl=list(T); B_=2000; ge=0
    for _ in range(B_):
        rng.shuffle(Tl)
        m=max(chi2stat(v,Tl) for v in feats.values())
        if m>=beststat: ge+=1
    pv=Fraction(ge+1,B_+1)
    print(f"  p={p} n={n}: {len(feats)} cheap predictors x joint(e,y-par) [{len(set(T))} cells]  ->  max exact chi2={float(beststat):.3f} by '{best}'  family-wise perm p={float(pv):.4f}  (all {len(ds)} keys)")
