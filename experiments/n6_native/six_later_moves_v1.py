#!/usr/bin/env python3
"""Later moves. After a move the cascade sits at T = (k + 1/6)/x, an opening of the last setter x.
Checks at every step of every run (17,135 residual sets, [1,40]):
 (a) d is in the way at T  iff  d(6k+1) mod 6x is NOT in [x, 5x]   (residue criterion, Theorem 3.1);
 (b) the next setter is the in-the-way element with the latest next opening, where d's next opening
     after T is (N_d + 1/6)/d with N_d the integer nearest d*T (|d T - N_d| < 1/6);
 (c) records how the setter's opening index relates: next setter's lap N relative to d*T.
Exact Fractions."""
from fractions import Fraction as F
from collections import Counter
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s = l.split("\t")[0]
    rows.append(eval(s))
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
steps = mism_a = mism_b = 0; nblk = Counter()
for S in rows:
    t = F(1, 6 * S[0]); x, k = None, None
    while True:
        blk = [d for d in S if cd(d * t) < F(1, 6)]
        if x is not None:
            steps += 1
            pred = [d for d in S if not (x <= (d * (6 * k + 1)) % (6 * x) <= 5 * x)]
            mism_a += sorted(pred) != sorted(blk)
            nblk[len(blk)] += 1
        if not blk: break
        best = None
        for d in blk:
            N = round(d * t)
            assert abs(d * t - N) < F(1, 6)
            o = F(6 * N + 1, 6 * d)
            if best is None or o > best[0]: best = (o, d, N)
        # (b): cascade's own move is the max next opening (definition); recompute via ceil form and compare
        o2 = max((-((-(d * t - F(1, 6)).numerator) // (d * t - F(1, 6)).denominator) + F(1, 6)) / d for d in blk)
        mism_b += o2 != best[0]
        t, x, k = best[0], best[1], best[2]
print(f"later steps checked: {steps}; (a) mismatches residue-criterion vs direct blocking: {mism_a}; "
      f"(b) mismatches nearest-lap opening vs cascade's next opening: {mism_b}")
print("number of elements in the way after each move:", dict(sorted(nblk.items())))
