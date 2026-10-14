"""EdgeWitness and SolutionPair are stated over an arbitrary list of (modulus, L, U) triples --
no order appears.  So they apply at every order n, not just 8.  Instantiate and check.

At order n the clear interval is I_n(b) = [ceil((b-1)/n), floor(((n-1)b - 1)/n)].
"""
from itertools import combinations
import random

def I(b, n): return (-(-(b-1)//n), ((n-1)*b - 1)//n)
def ok(q, m, bs, n): return all(I(b,n)[0] <= q % b <= I(b,n)[1] for b in bs + [m])

rng = random.Random(20260919)
print(f"{'n':>3} {'profiles':>9} {'with witness':>13} {'no edge witness':>16} {'singletons':>11}")
for n in (7, 8, 9, 11, 13):
    tot=0; wit=0; noedge=0; single=0
    for m in range(24, 150):
        ds=[d for d in range(2,m) if m%d==0]
        if len(ds) < 5: continue
        combos = list(combinations(ds,5))
        if len(combos) > 60: combos = rng.sample(combos, 60)
        for c in combos:
            bs=sorted(c); tot+=1
            S=[q for q in range(m) if ok(q,m,bs,n)]
            if not S: continue
            wit+=1
            if len(S)==1: single+=1
            if not any(q % b in I(b,n) for q in S for b in bs+[m]): noedge+=1
    print(f"{n:>3} {tot:>9,} {wit:>13,} {noedge:>16,} {single:>11,}")
print()
print("  EdgeWitness predicts 'no edge witness' = 0 at every order (it is order-agnostic).")
print("  SolutionPair predicts singletons only when S is the single reflection-centre point.")
