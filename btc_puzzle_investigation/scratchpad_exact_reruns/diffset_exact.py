# EXACT check of difference_set_closure: (1) Fourier factorization identity EXACT? (2) closure bound decay.
import mpmath as mp
mp.mp.dps=30
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
def dft(v,n):  # exact-data high-precision DFT: V[a]=sum_d v[d] e^{-2pi i a d/n}
    return [sum(v[d]*mp.e**(-2j*mp.pi*a*d/n) for d in range(n)) for a in range(n)]
for p in [43,67,163]:
    A_,B_=0,7
    pts=[(x,y) for x in range(p) for y in range(p) if (y*y-x*x*x-A_*x-B_)%p==0]
    n=len(pts)+1
    if not isprime(n): continue
    G=pts[0];P=[None]*n;Q=None
    for d in range(1,n):Q=ec_add(Q,G,A_,p);P[d]=Q
    X=[0]+[P[d][0] for d in range(1,n)]; Y=[0]+[P[d][1] for d in range(1,n)]
    def ch(b,c):
        v=[mp.mpc(0)]+[mp.e**(2j*mp.pi*((b*X[d]+c*Y[d])%p)/p) for d in range(1,n)]
        return v
    A=ch(3,1); B=ch(5,2); C=ch(7,4)
    Ah=dft(A,n); Bh=dft(B,n); Ch=dft(C,n)
    # S(a,b)=sum_{d} A[d]B[d]C[(a? )]... follow the code: S=fft2(outer(A,B)*C[idx]), idx=(i+j)%n
    # S[a,b]=sum_{i,j} A[i]B[j]C[(i+j)%n] e^{-2pi i(a i+b j)/n}
    def S_ab(a,b):
        return sum(A[i]*B[j]*C[(i+j)%n]*mp.e**(-2j*mp.pi*(a*i+b*j)/n) for i in range(n) for j in range(n))
    # identity RHS: (1/n) sum_m Ch[m] Ah[(a-m)%n] Bh[(b-m)%n]
    def RHS(a,b):
        return sum(Ch[m]*Ah[(a-m)%n]*Bh[(b-m)%n] for m in range(n))/n
    err=max(abs(S_ab(a,b)-RHS(a,b)) for a in (0,1,2) for b in (0,1,3))
    # closure bound: max|S|/n^2 (claim O(p^-1/2))
    mx=max(abs(S_ab(a,b)) for a in range(min(n,8)) for b in range(min(n,8)))
    print(f"p={p} n={n}: factorization identity err = {mp.nstr(err,4)} (should be 0)  |  sampled max|S|/n^2 = {mp.nstr(mx/n**2,5)}  (vs 1/sqrt(p)={float(1/mp.sqrt(p)):.4f})")
