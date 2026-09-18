"""sec 6.9 records that j (the number of non-integer ratios) does NOT predict whether a flank is
shadowed.  Candidate replacement index: the effective step  ghat = min(f, 1-f)  of each walker.
Two-walker counterexamples all sit at ghat = 1/2; run-length closes ghat < 1/4.
Does ghat predict shadowing at j = 2..6 as well?  Exact Fraction."""
import random
from fractions import Fraction as F
from math import floor
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def ghat(f): return min(f,1-f)
def shadowed(ws,KMAX=1500):
    """ws = list of (f, c).  returns min clear k, or None"""
    for k in range(KMAX+1):
        if all(circd(F(k)*f+c)>=TH for f,c in ws): return k
    return None

rng=random.Random(2026)
print(f"   {'j':>3} {'bucket by max ghat':>22} {'n':>7} {'shadowed':>9} {'rate':>9} {'max min-k':>10}")
for j in range(2,7):
    buckets={}
    for _ in range(12000):
        ws=[]
        for _ in range(j):
            f=F(rng.randint(1,999),1000)
            A=rng.randrange(8)
            ws.append((f,(F(A)+f)/8))
        g=max(ghat(f) for f,_ in ws)
        b = "< 1/4" if g<F(1,4) else ("[1/4,3/8)" if g<F(3,8) else "[3/8,1/2]")
        k=shadowed(ws)
        d=buckets.setdefault(b,[0,0,0])
        d[0]+=1
        if k is None: d[1]+=1
        else: d[2]=max(d[2],k)
    for b in ["< 1/4","[1/4,3/8)","[3/8,1/2]"]:
        if b in buckets:
            n,s,mk=buckets[b]
            print(f"   {j:>3} {b:>22} {n:>7} {s:>9} {s/n:>9.5f} {mk:>10}")
    print()

print("=== and the same populations indexed by j alone, for comparison ===")
rng=random.Random(2026)
for j in range(2,7):
    n=0; s=0
    for _ in range(12000):
        ws=[]
        for _ in range(j):
            f=F(rng.randint(1,999),1000); A=rng.randrange(8)
            ws.append((f,(F(A)+f)/8))
        n+=1
        if shadowed(ws) is None: s+=1
    print(f"   j = {j}:  shadowed {s}/{n} = {s/n:.5f}")
