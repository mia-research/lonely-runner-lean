#!/usr/bin/env python3
"""Observation: BHK case S7 (generic), sets where the cascade ends at an opening of v3 (size rank 3).
Does the clear lap of v3 beginning at T, [T, T + 2/(3 v3)], contain a meeting time k/D of runners 2 and 3
(D = v3 - v2)?  Control: the fraction of all clear laps of v3 in one period, [(k+1/6)/v3, (k+5/6)/v3],
k < v3, that contain a multiple of 1/D. Also the same for sets ending at other flanks (the lap of v3
containing T, if T lies in one). Reads six_cascade_observe_v1.tsv. Exact Fractions."""
import math
from fractions import Fraction as F
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s, c, m, ranks, laps, T, fr = l.rstrip("\n").split("\t")
    rows.append((eval(s), c, int(fr), F(T)))
def lap_has_meeting(lo, hi, D):
    k = -((-(lo * D).numerator) // (lo * D).denominator)   # ceil(lo*D)
    return F(k, D) <= hi
for case in ("S7", "S6", "S5", "S8"):
    for which in ("rank3", "other"):
        n = hit = 0; ctrl = 0.0
        for S, c, fr, T in rows:
            if c != case: continue
            if (fr == 3) != (which == "rank3"): continue
            v2, v3 = S[1], S[2]; D = v3 - v2
            x = v3 * T; k = x.numerator // x.denominator; frac = x - k
            if not (F(1, 6) <= frac <= F(5, 6)): continue
            lo, hi = (k + F(1, 6)) / v3, (k + F(5, 6)) / v3
            n += 1; hit += lap_has_meeting(lo, hi, D)
            ctrl += sum(lap_has_meeting((j + F(1, 6)) / v3, (j + F(5, 6)) / v3, D) for j in range(v3)) / v3
        if n: print(f"{case} {which:6s}: sets={n}; v3-lap at T contains a meeting time: {hit/n:.3f}; control (all v3 laps): {ctrl/n:.3f}")
