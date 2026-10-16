#!/usr/bin/env python3
"""Correction of E87's failure readout, and what the 16 unclosed §5/§6 sets are. For each: the full lonely set in one
period (exact intervals and isolated points), the widest interval's width x v1 and its lap vector; residues mod 6;
for the run family (1, 3k+2, ..., 3k+5), the lap vector of each interval as k grows (looking for a pattern in k)."""
from fractions import Fraction as F
def lonely(S):
    P = F(1)  # integer speeds: period 1
    pts = sorted(set([F(0), P] + [F(6 * k + j, 6 * d) for d in S for k in range(d) for j in (1, 5)]))
    lon = lambda t: all(F(1, 6) <= (d * t) % 1 <= F(5, 6) for d in S)
    iv = [(a, b) for a, b in zip(pts, pts[1:]) if lon((a + b) / 2)]
    pt = [a for a in pts if lon(a) and not any(x <= a <= y for x, y in iv)]
    return iv, pt
def laps(S, t): return tuple((d * t).numerator // (d * t).denominator for d in S)
fails = [(1,3,4,5,9),(1,4,5,6,9),(1,4,5,6,10),(1,4,5,6,12),(1,4,5,6,13),(1,5,6,7,8),(1,8,9,10,11),(1,11,12,13,14),
         (1,14,15,16,17),(1,17,18,19,20),(1,20,21,22,23),(2,5,7,9,15)]
for S in fails:
    iv, pt = lonely(S)
    if iv:
        a, b = max(iv, key=lambda z: z[1] - z[0]); w = (b - a) * S[0]
        print(S, "residues", tuple(d % 6 for d in S), f"intervals {len(iv)}, widest width*v1 = {w} at laps {laps(S, (a+b)/2)} [{a},{b}]; points {[str(x) for x in pt]}")
    else:
        print(S, "residues", tuple(d % 6 for d in S), "no interval; points", [str(x) for x in pt])
print("run family (1, 3k+2..3k+5):")
for k in range(1, 12):
    S = (1, 3 * k + 2, 3 * k + 3, 3 * k + 4, 3 * k + 5)
    iv, pt = lonely(S)
    first = iv[0] if iv else None
    print(f"  k={k} {S}: {len(iv)} intervals; first {first and (str(first[0]), str(first[1]), str(first[1]-first[0]))} laps {first and laps(S, (first[0]+first[1])/2)}")
