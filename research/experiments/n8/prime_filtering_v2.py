"""v1: BS's union bound certifies 76.5% of n=8 subjects, ratios quantised at k/4.
The 23.5% that fail are the question: is a good multiplier ABSENT there, or is the union bound
merely lossy because the BAD sets overlap?

BS's 40 pages at n=7 are exactly the second case -- when counting fails they exploit the level
structure and the correlations.  So measure the two apart:

    union bound  :  sum_d |BAD(d)|  <  |U|            (lossy, what v1 measured)
    truth        :  |union_d BAD(d)| <  |U|           (a good multiplier really exists)

If the truth holds wherever the bound fails, the gap at n=8 is counting slack, not absence.
Counting over a finite group throughout.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from math import gcd
import random
from collections import Counter
NR=8
def analyse(ds,M):
    """Return (sum of |BAD|, |union BAD|, |U|) at modulus N = 8M."""
    N=NR*M
    U=[l for l in range(1,N) if gcd(l,N)==1]
    tot=0; union=set()
    for d in ds:
        dm=d%N
        for l in U:
            r=(l*dm)%N
            if min(r,N-r)*NR<N: tot+=1; union.add(l)
    return tot,len(union),len(U)
rng=random.Random(2222)
MR=range(1,61)
n_bound=n_truth=n_tot=0
fail_but_true=0; fail_and_false=0
surv=Counter(); slack=[]
for _ in range(150):
    v=speeds(rng.sample(range(1,90),NR))
    for i in range(NR):
        ds=[abs(v[j]-v[i]) for j in range(NR) if j!=i]
        g=0
        for x in ds: g=gcd(g,x)
        ds=[x//g for x in ds]
        bestb=9e9; bestt=None
        for M in MR:
            t,u,U=analyse(ds,M)
            if t/U<bestb: bestb=t/U
            if u<U: bestt=(M,u,U)          # a good multiplier exists at this modulus
        n_tot+=1
        ok_b = bestb<1
        ok_t = bestt is not None
        n_bound+=ok_b; n_truth+=ok_t
        surv[round(bestb*4)]+=1
        if not ok_b and ok_t: fail_but_true+=1
        if not ok_b and not ok_t: fail_and_false+=1
        if ok_t: slack.append(bestt[1]/bestt[2])
print(f"  {n_tot} subjects, modulus N = 8M, M = 1..60\n")
print(f"  BS union bound certifies              : {n_bound} of {n_tot}   ({n_bound/n_tot:.4f})")
print(f"  a good multiplier ACTUALLY exists     : {n_truth} of {n_tot}   ({n_truth/n_tot:.4f})")
print(f"  bound fails but multiplier exists     : {fail_but_true}")
print(f"  bound fails AND no multiplier found   : {fail_and_false}")
print(f"\n  uncaged-disparity count (ratio*4): {dict(sorted(surv.items()))}")
if slack:
    slack.sort()
    print(f"  |union BAD| / |U| where a multiplier exists: min {slack[0]:.3f}  median {slack[len(slack)//2]:.3f}  max {slack[-1]:.3f}")
