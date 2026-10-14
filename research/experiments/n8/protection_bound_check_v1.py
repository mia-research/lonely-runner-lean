"""Exact check of the cumulative protection bound (owner's pasted idea, 2026-10-07).  Exact Fractions.
Claim tested: let b be the setter of the move into state t_i (so b*t_i = P + 1/8 exactly).  For the later states
t_j (j > i), if  sum_{k=i+1..j} b/x_k <= 3  (x_k the setter of the move into t_k)  then b is NOT in the way at t_j.
Also the contrapositive count: every time b IS in the way at a later state, the sum exceeds 3.
Population: every 7-subset of [1,N], gcd 1 (disparity sets of the subject; readings = disparities / d_min)."""
import sys
from fractions import Fraction as F
from itertools import combinations
from math import gcd, floor
from functools import reduce
N = int(sys.argv[1]) if len(sys.argv) > 1 else 20
def inway(d, t):
    x = d*t
    return abs(x - floor(x + F(1,2))) < F(1,8)
tests = viol = recapture = tight = 0
max_sum_ok = F(0); min_sum_recap = None
for S in combinations(range(1, N+1), 7):
    if reduce(gcd, S) != 1: continue
    m = S[0]
    t = F(1, 8*m)
    states = [t]; setters = [None]
    while True:
        blk = [(d, floor(d*t + F(1,2))) for d in S if inway(d, t)]
        if not blk: break
        best = max(((F(8*z+1, 8*d)), d) for d, z in blk)
        t = best[0]; states.append(t); setters.append(best[1])
        if len(states) > 200: break
    for i in range(1, len(states)):
        b = setters[i]
        acc = F(0)
        for j in range(i+1, len(states)):
            acc += F(b, setters[j])
            tests += 1
            ib = inway(b, states[j])
            if acc <= 3 and ib: viol += 1
            if ib:
                recapture += 1
                if min_sum_recap is None or acc < min_sum_recap: min_sum_recap = acc
            if acc <= 3 and not ib and acc > max_sum_ok: max_sum_ok = acc
print("N =", N, " (b, later state) tests:", tests, " violations of 'sum<=3 => clear':", viol)
print("recaptures (b in the way again at a later state):", recapture, " smallest sum at a recapture:", min_sum_recap, "=", float(min_sum_recap) if min_sum_recap is not None else None)
