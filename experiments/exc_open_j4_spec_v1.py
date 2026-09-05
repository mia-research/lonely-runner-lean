"""Derive exact read-off specs for the |j|=4 transversals (3,4),(3,-4),(5,-4).
Relation j*r ≡ i*p (mod q); write |j|*r = iota*p + gamma*q (iota=sign(j)*i, gamma>0 per c).
At half-int t=(m+1/2)/q: X={r t}, A={p t}, slope = iota/4.
We find, per (i,j,c): the selector rho = (4*floor(p t) - extra) pattern and the line
X = (iota/4)*A + beta, plus the A-window, validated on all sample triples."""
from math import gcd
from fractions import Fraction as F
def frac(x): return x-(x.numerator//x.denominator)
def floorf(x): return x.numerator//x.denominator
def Cp(a,q,m): return F((2*(a*m%q)+a)%(2*q), 2*q)
def in_R(X,Y): return F(1,6)<=X<=F(1,2) and F(1,6)<=Y<=F(1,3)

def pt(p,q,m): return F(p,q)*(F(2*m+1,2))  # p*t

for (i,j) in [(3,4),(3,-4),(5,-4)]:
    N=abs(j)
    print(f"\n##### (i,j)=({i},{j}) N={N}")
    # group sample triples by c=(j*r-i*p)/q
    bycs={}
    for q in range(30,55):
        for p in range(1,q):
            if 3*p>=q or gcd(p,q)!=1: continue
            for r in range(q+1,(3*q)//2+1):
                if 2*r>=3*q or r==p+q: continue
                if (j*r-i*p)%q!=0: continue
                c=(j*r-i*p)//q
                bycs.setdefault(c,[]).append((p,q,r))
    for c in sorted(bycs):
        gamma = (N*0)  # |j|r = iota p + gamma q ; from j r - i p = c q:
        # j>0: j r = i p + c q -> iota=i, gamma=c.  j<0: -N r = i p + c q -> N r = -i p - c q,
        #   gamma=-c>0, iota=-i.
        if j>0: iota, gamma = i, c
        else: iota, gamma = -i, -c
        trips=bycs[c]
        # for each triple find R-witness m, record (floor(pt) mod 4, m mod 4, A, X)
        # infer beta = X - (iota/4)*A and selector key = (4*floor(pt) - 2*S) where...
        recs=[]
        for (p,q,r) in trips:
            for m in range(2*q):
                X=Cp(r,q,m); A=Cp(p,q,m)
                if in_R(X,A):
                    fl=floorf(pt(p,q,m))
                    beta = X - F(iota,4)*A
                    # selector value rho' = (2S+gamma) mod 8 where S=iota*fl+gamma*m
                    S=iota*fl+gamma*m
                    rhop=(2*S+gamma)%(2*N)
                    recs.append((p,q,r,m,fl%4,m%4,beta,rhop,A))
                    break
        betas=set(F(b) for *_,b,_,_ in recs)
        rhops=set(rp for *_,rp,_ in recs)
        Amin=min(a for *_,a in recs); Amax=max(a for *_,a in recs)
        print(f"  c={c}: iota={iota} gamma={gamma} | #triples={len(trips)} matched={len(recs)}")
        print(f"     line X=({iota}/4)A+beta betas={betas}  rho'(=2S+g mod8)={sorted(rhops)}")
        print(f"     A-window seen [{float(Amin):.3f},{float(Amax):.3f}]")
