"""Theorem 6.8: the subject is lonely iff SOME flank has a lonely opening.
So a shadowed flank is harmless; the question is whether a SUBJECT can have all 7 flanks shadowed,
and whether an ARRANGEMENT can have all 8 subjects so.

Measure the distribution of clear flanks per subject."""
from fractions import Fraction as F
from collections import Counter
import random

def frac(r): return r - (r.numerator // r.denominator)

def flank_clear(ratios, kmax=600):
    ints = [r for r in ratios if r.denominator == 1]
    if any(int(r) % 8 == 0 for r in ints): return False      # not live: dead flank
    movers = [r for r in ratios if r.denominator != 1]
    for k in range(kmax):
        ok = True
        for r in movers:
            x = k*frac(r) + r/8
            if abs(x - F(round(float(x)))) < F(1,8): ok = False; break
        if ok: return True
    return False

rng = random.Random(20260919)
per_subject = Counter(); worst_arr = []; arr_all_shadowed = 0; tot_arr = 0
for _ in range(4000):
    v = sorted(rng.sample(range(0, 300), 8))
    tot_arr += 1
    lonely_subjects = 0
    minclear = 99
    for i in range(8):
        ds = [v[j] - v[i] for j in range(8) if j != i]
        nclear = 0
        for e in ds:
            if e == 0: continue
            if flank_clear([F(d, abs(e)) for d in ds]): nclear += 1
        per_subject[nclear] += 1
        minclear = min(minclear, nclear)
        if nclear > 0: lonely_subjects += 1
    if lonely_subjects == 0:
        arr_all_shadowed += 1
        if len(worst_arr) < 3: worst_arr.append(v)
print(f"arrangements: {tot_arr:,}   subjects: {tot_arr*8:,}\n")
print(f"  clear flanks per subject (out of 7): {dict(sorted(per_subject.items()))}")
z = per_subject[0]
print(f"\n  subjects with ZERO clear flanks (not lonely)   : {z:,}"
      f"  ({100*z/(tot_arr*8):.3f}%)")
print(f"  arrangements where NO subject is lonely       : {arr_all_shadowed:,}")
for v in worst_arr: print(f"     {v}")
