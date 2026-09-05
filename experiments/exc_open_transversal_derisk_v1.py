"""De-risk the 9 read-off transversals in exc_open.
Relation (from exc_relation): q | (j*r - i*p), i.e. j*r ≡ i*p (mod q).
Cone: q>=30, gcd(p,q)=1, 3p<q, q<r<3q/2 (2r<3q), r≠p+q.
For each (i,j): enumerate valid (p,q,r), group by c (=(|j|r ∓ i p)/q), and for each
check existence of a half-integer m with (X,A) in R=[1/6,1/2]x[1/6,1/3],
where X={r(m+½)/q}, A={p(m+½)/q}. Report c-values, parity, R-coverage."""
from math import gcd
from fractions import Fraction as F
def Cpoint(a,q,m): return F((2*(a*m%q)+a)%(2*q), 2*q)
def in_R(X,Y): return F(1,6)<=X<=F(1,2) and F(1,6)<=Y<=F(1,3)

TRANS=[(2,3),(2,-3),(3,4),(3,-4),(4,3),(4,-3),(5,3),(5,-3),(5,-4)]

for (i,j) in TRANS:
    print(f"\n##### (i,j)=({i},{j})  relation: {j}*r ≡ {i}*p (mod q)")
    cvals={}
    total=0; Rwit=0; nowit=[]
    parities={'p_even':0,'p_odd':0}
    for q in range(30,73):
        for p in range(1,q):
            if 3*p>=q or gcd(p,q)!=1: continue
            for r in range(q+1,(3*q+1)//2):
                if 2*r>=3*q: continue
                if r==p+q: continue
                if (j*r - i*p) % q != 0: continue
                # c = (j*r - i*p)/q  (could be neg if j<0)
                c=(j*r-i*p)//q
                cvals[c]=cvals.get(c,0)+1
                total+=1
                mR=next((m for m in range(2*q) if in_R(Cpoint(r,q,m),Cpoint(p,q,m))),None)
                if mR is not None: Rwit+=1
                else: nowit.append((p,q,r,c))
                parities['p_even' if p%2==0 else 'p_odd']+=1
    print(f"  total valid triples: {total}; c-distribution: {dict(sorted(cvals.items()))}")
    print(f"  R-witness coverage: {Rwit}/{total}; parity: {parities}")
    if nowit:
        print(f"  NO R-witness ({len(nowit)}): first few {nowit[:6]}")
