"""Counting needs mean blockers-per-candidate < 1.  Removing self and unit takes 7 -> 5 readings.
Is the true per-reading blocking density 1/4, or less?  Measure it exactly."""
import random
from fractions import Fraction as F

def cands(sk):
    A = sk + ((1-sk) % 8); out = []
    while A <= 7*sk: out.append(A); A += 8
    return out

rng = random.Random(20260919)
pairs = blocked = 0
zero_blocker = tot_cand = 0
hist = {}
for _ in range(4000):
    S = [1] + sorted(rng.sample(range(2, 60), 6))
    for sk in S:
        for A in cands(sk):
            tot_cand += 1; c = 0
            for si in S:
                if si == sk or si == 1: continue      # proved never to block
                pairs += 1
                M = 8*sk; r = (si*A) % M
                if min(r, M-r) < sk: blocked += 1; c += 1
            hist[c] = hist.get(c, 0) + 1
            if c == 0: zero_blocker += 1
print(f"eligible (candidate, reading) pairs : {pairs:,}")
print(f"  of which blocking                 : {blocked:,}   density {blocked/pairs:.4f}"
      f"   (the heuristic says 0.25)")
print(f"  mean blockers per candidate       : {blocked/tot_cand:.4f}   (counting needs < 1)")
print(f"\n  candidates by blocker count: {dict(sorted(hist.items()))}")
print(f"  candidates with ZERO blockers = witnesses: {zero_blocker:,} of {tot_cand:,}"
      f"   ({100*zero_blocker/tot_cand:.2f}%)")
