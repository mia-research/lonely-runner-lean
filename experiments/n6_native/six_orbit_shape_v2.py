#!/usr/bin/env python3
"""Observation only, follow-up to six_orbit_shape_v1. (a) Is the cascade's own threshold for runners 2, 3 the
rate 3 v1 (BHK S8) or 5 v1? Cross-tab first setter / any setter in {2,3} against v3 <= 3v1, 3v1 < v3 < 5v1,
v3 >= 5v1 (and v2 likewise). (b) The 12 sets whose final instant is a 2-3 meeting time, listed in full.
(c) Final flank 3 by orbit class with v3/v1 band."""
from fractions import Fraction as F
from collections import Counter
from math import gcd
exec(open("six_orbit_shape_v1.py").read().split("cls_feat =")[0])
tab = Counter(); meet = []; ff3 = Counter()
for S, c in rows:
    v1, v2, v3 = S[:3]
    band3 = "v3<=3v1" if v3 <= 3*v1 else ("3v1<v3<5v1" if v3 < 5*v1 else "v3>=5v1")
    band2 = "v2<5v1" if v2 < 5*v1 else "v2>=5v1"
    path, T = walk(S)
    first = path[0][0] if path else 0
    any23 = any(r in (2, 3) for r, _ in path)
    tab[(band3, band2, "first in {2,3}" if first in (2, 3) else "first not", "some setter in {2,3}" if any23 else "none")] += 1
    rate, o, n = shape(S)
    if (T * (v3 - v2)).denominator == 1:
        meet.append((S, o, n, T, path, [str((d * T) % 1) for d in S]))
    ff3[(o, band3, "ff=3" if path and path[-1][0] == 3 else "ff!=3")] += 1
print("(a) band of v3, band of v2, first setter, any setter in {2,3}: count")
for k in sorted(tab): print("  ", k, tab[k])
print(f"(b) final instant at a 2-3 meeting time: {len(meet)}")
for m in meet: print("  ", m[0], m[1], "n=", m[2], "T=", m[3], "path", m[4], "readings", m[5])
print("(c) final flank 3 by orbit class and v3 band")
for k in sorted(ff3): print("  ", k, ff3[k])
