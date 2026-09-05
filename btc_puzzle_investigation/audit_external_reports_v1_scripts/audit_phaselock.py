# AUDIT 2: compute A_new Frobenius eigenvalues via point-counting the cover C:w^4=f(x),
# then TEST the claimed 120-degree (zeta_3) phase-lock alpha2 = conj(alpha1)*zeta3.
import numpy as np, cmath, math
from sympy import legendre_symbol, isprime

def build_field(p,k):
    # F_{p^k} elements as tuples of length k (low->high coeffs); need irreducible modulus poly
    def is_irr(mod):
        # degree k poly (list len k+1, monic). irreducible over F_p for k<=3 iff no roots (k=2,3)
        if k==1: return True
        for x in range(p):
            v=sum(mod[i]*pow(x,i,p) for i in range(k+1))%p
            if v==0: return False
        return True
    import itertools
    mod=None
    for coeffs in itertools.product(range(p),repeat=k):
        m=list(coeffs)+[1]
        if is_irr(m): mod=m; break
    def mul(a,b):
        r=[0]*(2*k-1)
        for i in range(k):
            if a[i]:
                for j in range(k):
                    r[i+j]=(r[i+j]+a[i]*b[j])%p
        # reduce mod 'mod' (monic degree k)
        for d in range(2*k-2,k-1,-1):
            c=r[d]
            if c:
                r[d]=0
                for i in range(k):
                    r[d-k+i]=(r[d-k+i]-c*mod[i])%p
        return tuple(r[:k])
    return mod,mul

def count_cover(p,A,B,k):
    mod,mul=build_field(p,k)
    q=p**k
    def to_tuple(n):
        t=[]
        for _ in range(k): t.append(n%p); n//=p
        return tuple(t)
    els=[to_tuple(n) for n in range(q)]
    # tally 4th powers
    from collections import Counter
    cnt4=Counter()
    for w in els:
        w4=mul(mul(w,w),mul(w,w))
        cnt4[w4]+=1
    zero=tuple([0]*k)
    # f(x)=x^3+Ax+B as field element
    Af=to_tuple(A%p); Bf=to_tuple(B%p)
    def fval(x):
        x2=mul(x,x); x3=mul(x2,x)
        # x3 + A*x + B
        Ax=mul(Af,x)
        r=list(x3)
        for i in range(k): r[i]=(r[i]+Ax[i]+Bf[i])%p
        return tuple(r)
    Naff=0
    for x in els:
        Naff+=cnt4[fval(x)]
    return Naff+1  # one point at infinity (gcd(4,3)=1)

def ecount(p,A,B):
    c=1
    for x in range(p):
        r=(x**3+A*x+B)%p
        c+=(1+int(legendre_symbol(r,p))) if r%p!=0 else 1
    return c

def anew_eigs(p,A,B):
    N1=count_cover(p,A,B,1);N2=count_cover(p,A,B,2);N3=count_cover(p,A,B,3)
    t1=p+1-N1; t2=p*p+1-N2; t3=p**3+1-N3
    e1=t1
    e2=(e1*t1-t2)//2
    e3=(e2*t1-e1*t2+t3)//3
    # char poly of Frobenius (degree 6), functional eq: e4=p*e2, e5=p^2*e1, e6=p^3
    P=[1,-e1,e2,-e3,p*e2,-p*p*e1,p**3]  # coeffs high->low of T^6...const
    aE=p+1-ecount(p,A,B)
    # divide P by (T^2 - aE T + p)
    div=[1,-aE,p]
    # polynomial long division
    rem=P[:]; quo=[]
    for i in range(len(P)-len(div)+1):
        c=rem[i]
        quo.append(c)
        for j in range(len(div)):
            rem[i+j]-=c*div[j]
    quartic=quo  # A_new char poly, degree 4
    roots=np.roots(quartic)
    return roots,aE,quartic

print("Testing zeta_3 phase-lock: A_new eigenvalues should pair as {a, conj(a), conj(a)*z3, a*conj(z3)}")
print("i.e. among 4 angles theta_i, one pair is the other pair rotated by +-120 deg.\n")
for p,A,B,typ in [(13,3,7,'nonCM p=1mod4'),(29,4,9,'nonCM p=1mod4'),(37,3,15,'nonCM p=1mod4'),
                   (43,0,7,'CM p=3mod4'),(11,0,7,'CM p=3mod4'),(23,1,3,'nonCM p=3mod4')]:
    try:
        roots,aE,quартic=anew_eigs(p,A,B)
    except Exception as e:
        print(f"p={p} {typ}: err {e}"); continue
    mags=np.abs(roots); angs=np.sort(np.degrees(np.angle(roots)))%360
    okmag=np.allclose(mags,math.sqrt(p),rtol=1e-6)
    # test 120-deg structure: check all pairwise angle-diffs for ~120 mod 360
    diffs=[]
    n=len(roots)
    for i in range(n):
        for j in range(n):
            if i!=j:
                d=(np.degrees(np.angle(roots[i]/np.conj(roots[j]))))%360
                diffs.append(round(d,1))
    has120=any(abs(((d-120+180)%360)-180)<1.0 or abs(((d-240+180)%360)-180)<1.0 for d in diffs)
    print(f"p={p:3d} {typ:16s}: |eig|=sqrt(p)? {okmag}  angles={np.round(angs,1)}  aE={aE}  120deg-pair? {has120}")
