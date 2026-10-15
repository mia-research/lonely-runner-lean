#!/usr/bin/env python3
"""Observation only. Does the cascade separate SixResidual sets along BHK's split, read as orbit shape + one rate?
For each set (six_cascade_observe_v1.tsv, primitive SixResidual, max <= 40), D = v3 - v2, g = gcd(D, v3, v1),
n = D/g, c3 = v3/g, c1 = v1/g. Orbit <(c3, c1)> in (Z/n)^2:
  axis1 = runner 1 back at a whole lap at t0 = 1/D  (n | c1, i.e. D | v1)   -- BHK S5
  axis3 = runner 3 back at a whole lap at t0          (n | c3, i.e. D | v3)  -- BHK S6 (when not axis1)
  open  = neither; exc = G4 (n=4, c3=2, c1 odd) or G7 (n=7, c3 = 2 c1 mod 7, c1 != 0)
Rate: fast1 = v3 <= 3 v1 (BHK S8).
Cascade (exact Fractions, from 1/(6 v1)): path of (setter rank, opening k); final instant T.
Recorded at T: which pairs (i<j) share a reading (T (vj - vi) whole), with emphasis on pair (2,3);
final flank rank, first setter, moves, v1 T < 1/3.
Prints distributions per class and, conversely, class composition per cascade feature."""
from fractions import Fraction as F
from collections import Counter, defaultdict
from math import gcd
rows = [(eval(l.split("\t")[0]), l.split("\t")[1]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def walk(S):
    t = F(1, 6 * S[0]); path = []
    while True:
        blk = [d for d in S if cd(d * t) < F(1, 6)]
        if not blk: return path, t
        best = None
        for d in blk:
            N = round(d * t); o = F(6 * N + 1, 6 * d)
            if best is None or o > best[0]: best = (o, d, N)
        t = best[0]; path.append((S.index(best[1]) + 1, best[2]))
def shape(S):
    v1, v2, v3 = S[:3]; D = v3 - v2; g = gcd(D, gcd(v3, v1)); n, c3, c1 = D // g, v3 // g, v1 // g
    if v3 <= 3 * v1: rate = "fast1"
    else: rate = "slow1"
    if c1 % n == 0: o = "axis1"
    elif c3 % n == 0: o = "axis3"
    elif n == 4 and c3 % 4 == 2 and c1 % 2 == 1: o = "G4"
    elif n == 7 and c1 % 7 and c3 % 7 == (2 * c1) % 7: o = "G7"
    else: o = "open"
    return rate, o, n
cls_feat = defaultdict(lambda: defaultdict(Counter)); feat_cls = defaultdict(lambda: defaultdict(Counter))
mism = 0; ncls = Counter()
for S, c in rows:
    rate, o, n = shape(S)
    cls = "S8" if rate == "fast1" else {"axis1": "S5", "axis3": "S6"}.get(o, "S7")
    mism += cls != c
    key = f"{rate}/{o}"; ncls[key] += 1
    path, T = walk(S)
    shared = tuple(f"{i+1}{j+1}" for i in range(5) for j in range(i + 1, 5) if (T * (S[j] - S[i])).denominator == 1)
    feats = {
        "final_flank": path[-1][0] if path else 1,
        "first_setter": path[0][0] if path else 0,
        "moves": min(len(path), 4),
        "early": S[0] * T < F(1, 3),
        "23_meet_at_T": "23" in shared,
        "pairs_meeting_at_T": shared if shared else "-",
        "T_multiple_of_1/D": (T * (S[2] - S[1])).denominator == 1,
        "r1_reading_x6": int(6 * ((S[0] * T) % 1)),  # sixth of the lap runner 1 sits in at T
    }
    for f, v in feats.items():
        cls_feat[key][f][v] += 1; feat_cls[f][v][key] += 1
print(f"sets: {len(rows)}; class by orbit/rate disagrees with tsv BHK label: {mism}")
print("class sizes:", dict(ncls)); print()
for key in sorted(ncls):
    print(f"== {key} ({ncls[key]})")
    for f in cls_feat[key]:
        tot = ncls[key]
        print(f"   {f}: " + ", ".join(f"{v}:{m}" for v, m in cls_feat[key][f].most_common(8)))
print()
print("== converse: class composition for each cascade feature value")
for f in ("final_flank", "first_setter", "moves", "early", "23_meet_at_T", "T_multiple_of_1/D", "r1_reading_x6"):
    for v in sorted(feat_cls[f], key=str):
        print(f"   {f}={v}: " + ", ".join(f"{k}:{m}" for k, m in sorted(feat_cls[f][v].items())))
