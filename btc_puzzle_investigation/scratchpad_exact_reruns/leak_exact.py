# EXACT leak-null rerun: MI(public feature ; d mod k) over ALL keys, integer contingency, exact perm null.
from fractions import Fraction
from collections import Counter
import random
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

def mi_exact(F, T):
    # exact mutual information (in bits) from integer-labeled arrays F,T via Fraction; returns (num,den) as Fraction of I in nats? use log via float ONLY at the very end for display, decision uses exact independence
    N=len(F); joint=Counter(zip(F,T)); mf=Counter(F); mt=Counter(T)
    # exact test of independence: chi-square numerator as integer (sum (Nij*N - Ni*Nj)^2 / (Ni*Nj)) -- keep as Fraction
    chi=Fraction(0)
    for i in mf:
        for j in mt:
            nij=joint.get((i,j),0)
            exp_num=mf[i]*mt[j]  # expected*N
            chi+=Fraction((nij*N-exp_num)**2, exp_num) if exp_num else 0
    chi/=N
    return chi, joint, mf, mt, N

def perm_pvalue(F,T,obs_chi,B=3000,seed=1):
    rng=random.Random(seed); Tl=list(T); ge=0
    for _ in range(B):
        rng.shuffle(Tl)
        c,_,_,_,_=mi_exact(F,Tl)
        if c>=obs_chi: ge+=1
    return Fraction(ge+1,B+1)

for p,A,B in [(43,0,7),(67,0,7),(103,0,7)]:
    pts=[(x,y) for x in range(p) for y in range(p) if (y*y-x*x*x-A*x-B)%p==0]
    n=len(pts)+1
    G=pts[0]; P=[None]*n; Q=None
    for d in range(1,n): Q=ec_add(Q,G,A,p); P[d]=Q
    # features (exact, integer): chi3(x)=x^((p-1)/3) label, y-parity
    for feat_name,k in [("chi3(x_P) ; d mod 3",3),("y-parity ; d mod 2",2)]:
        F=[]; T=[]
        for d in range(1,n):
            x,y=P[d]
            if "chi3" in feat_name:
                F.append(pow(x,(p-1)//3,p))
            else:
                F.append(y%2)
            T.append(d%k)
        chi,_,_,_,N=mi_exact(F,T)
        pv=perm_pvalue(F,T,chi)
        print(f"  p={p} n={n}: {feat_name:22}  exact chi^2-stat={float(chi):.4f}  perm p={float(pv):.4f}  (N={N} keys, ALL enumerated)")
    print()
