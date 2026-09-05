"""
v4: Is the 2D witness tractable via "slack grows with q"?
Test: among q>=6i tuples, how does witness-count scale? Are TIGHT tuples
(<=2 witnesses) bounded in q? If tight tuples have q <= some modest bound,
the proof could split: large q (clean lower bound >=1) + small q (finite check).

Also: lower bound on count. C-points in R ~ q*area = q/18. Is count >= floor(q/18)-c?
"""
from math import gcd
from fractions import Fraction as F

def frac(x): return x - (x.numerator//x.denominator)
def P(m,p,q,r): return frac(F(r*m,2*q)), frac(F(p*m,2*q))
XLO,XHI=F(1,6),F(1,2); YLO,YHI=F(1,6),F(1,3)
def inR(X,Y): return XLO<=X<=XHI and YLO<=Y<=YHI
def has_readoff(i,p,q,r):
    for k in range(q):
        if (k*r-i)%q==0 and (k*p+i)%q==0: return k
    return None
def valid_tuples(QMAX):
    for i in (3,4,5):
        for q in range(18,QMAX+1):
            d=gcd(i,q)
            if d==1: continue
            for p in range(1,q):
                if 3*p>=q or gcd(p,q)!=1: continue
                for r in range(q+1,(3*q)//2+1):
                    if 2*r>=3*q: continue
                    k=has_readoff(i,p,q,r)
                    if k is None: continue
                    yield i,p,q,r,d,k
def count_wit(p,q,r): return sum(1 for m in range(1,2*q,2) if inR(*P(m,p,q,r)))

QMAX=240
tight_maxq={1:0,2:0,3:0}
worst_ratio=[]  # (count - q/18, ...) to see lower bound
min_count_by_q={}
n=0
for i,p,q,r,d,k in valid_tuples(QMAX):
    if q<6*i: continue
    n+=1
    c=count_wit(p,q,r)
    for thr in (1,2,3):
        if c<=thr: tight_maxq[thr]=max(tight_maxq[thr],q)
    min_count_by_q.setdefault(q, (c,i,p,r))
    if c < min_count_by_q[q][0]:
        min_count_by_q[q]=(c,i,p,r)
print(f"q>=6i tuples up to q={QMAX}: {n}")
print(f"max q with <=1 witness: {tight_maxq[1]}")
print(f"max q with <=2 witnesses: {tight_maxq[2]}")
print(f"max q with <=3 witnesses: {tight_maxq[3]}")

print("\nmin witness count per q (showing where min<=3, and the q/18 reference):")
for q in sorted(min_count_by_q):
    c,i,p,r=min_count_by_q[q]
    if c<=3 or q%30==0:
        print(f"  q={q}: min_count={c}  (q/18≈{q/18:.1f})  worst tuple i={i} p={p} r={r}")

# Does min_count grow unboundedly? print min_count for q in bands
print("\nmin count in q-bands:")
bands=[(18,30),(31,60),(61,90),(91,120),(121,180),(181,240)]
for lo,hi in bands:
    cs=[min_count_by_q[q][0] for q in min_count_by_q if lo<=q<=hi]
    if cs: print(f"  q in [{lo},{hi}]: min over tuples = {min(cs)}")
