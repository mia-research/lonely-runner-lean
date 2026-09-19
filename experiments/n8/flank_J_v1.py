"""The right object: FLANKS, not global readings.

A flank is a subject difference e; runner j has ratio rho_j = d_j/e.
Integer ratio A: clear at every opening iff 8 does not divide A; in the way always if 8 | A.
Non-integer ratio: only the fractional part moves.

Theorem 6.9 decides a live flank with |J| = 1 non-integer ratio.
Prop 6.10 decides |J| = 2 under a lattice condition.
So: does every arrangement have a LIVE flank with |J| <= 2 ?
"""
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
import random

def flanks(v):
    """v = sorted speeds (an arrangement). For each subject i and each difference e, the flank."""
    out = []
    for i in range(len(v)):
        ds = [v[j] - v[i] for j in range(len(v)) if j != i]
        for e in ds:
            if e == 0: continue
            ae = abs(e)
            ratios = [F(d, ae) for d in ds]
            live = not any(r.denominator == 1 and r.numerator % 8 == 0 for r in ratios)
            J = sum(1 for r in ratios if r.denominator != 1)
            out.append((live, J))
    return out

rng = random.Random(20260919)
minJ_live = Counter(); no_live = 0; tot = 0
worst = []
for _ in range(20000):
    v = sorted(rng.sample(range(0, 200), 8))
    fl = flanks(v)
    liveJ = [J for live, J in fl if live]
    tot += 1
    if not liveJ:
        no_live += 1; continue
    m = min(liveJ)
    minJ_live[m] += 1
    if m >= 3 and len(worst) < 5: worst.append((v, sorted(liveJ)[:8]))
print(f"random 8-speed arrangements: {tot:,}")
print(f"  arrangements with NO live flank : {no_live:,}")
print(f"  minimum |J| over live flanks    : {dict(sorted(minJ_live.items()))}")
print(f"\n  |J| <= 2 somewhere (decided by Thm 6.9 / Prop 6.10):"
      f" {sum(v for k,v in minJ_live.items() if k<=2):,}"
      f"  ({100*sum(v for k,v in minJ_live.items() if k<=2)/max(tot-no_live,1):.2f}%)")
if worst:
    print(f"\n  arrangements where EVERY live flank has |J| >= 3:")
    for v, js in worst: print(f"     {v}  live |J| = {js}")
