# y-channel cheap readouts vs ODD-preserving null (y is odd: y(P_d)=-y(P_{n-d})). Real leak or forced symmetry?
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
def rho(F):
    Fc=np.concatenate([[0.0],F]).astype(complex)
    l2=math.sqrt(np.mean(np.abs(Fc[1:])**2)) or 1e-12
    C=np.abs(np.fft.fft(Fc))/len(Fc);C[0]=0
    return C.max()/l2
rng=np.random.default_rng(5)
for p in [67,163]:
    A,B=0,7
    pts=[(x,y) for x in range(p) for y in range(p) if (y*y-x*x*x-A*x-B)%p==0]
    n=len(pts)+1
    if not isprime(n): continue
    G=pts[0];P=[None]*n;Q=None
    for d in range(1,n):Q=ec_add(Q,G,A,p);P[d]=Q
    odd_ok=all((P[d][1]+P[n-d][1])%p==0 for d in range(1,n))  # y_{P_d}=-y_{P_{n-d}}
    for nm,f in [('y-sign', lambda x,y:1.0 if y<p/2 else -1.0),('y-parity',lambda x,y:1.0 if y%2 else -1.0)]:
        Ft=np.array([f(P[d][0],P[d][1]) for d in range(1,n)]); rt=rho(Ft)
        half=(n-1)//2
        # ODD-preserving null: F_d=-F_{n-d}; shuffle the half-values AND their signs consistently
        pairvals=[Ft[d-1] for d in range(1,half+1)]
        ge_plain=0; ge_odd=0; B_=800
        for _ in range(B_):
            if rho(rng.permutation(Ft))>=rt: ge_plain+=1
            pv=rng.permutation(pairvals); Fs=np.zeros(n-1)
            for i,d in enumerate(range(1,half+1)):
                Fs[d-1]=pv[i]; Fs[(n-d)-1]=-pv[i]   # odd-preserving
            if rho(Fs)>=rt: ge_odd+=1
        pp=(ge_plain+1)/(B_+1); po=(ge_odd+1)/(B_+1)
        print(f"p={p} n={n} {nm:9} (y-odd forced={odd_ok}): true rho={rt:.4f}  plain-shuffle p={pp:.4f}  ODD-preserving p={po:.4f}  -> {'LEAK beyond y-odd sym' if po<0.02 else 'forced y-odd only (no leak)'}")
