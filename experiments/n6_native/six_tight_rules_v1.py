#!/usr/bin/env python3
"""Candidate rules for the unique good opening j* of the 46 tight sets (six_tight_dump_v1_100.txt),
each tested against the exact chance rate k/e (a rule proposing k of the e openings contains j* with
probability k/e under a uniformly placed j*).
  CASCADE: the cascade (MomentIterationN.move) on S from 1/(6 min S); proposes j if its fixed point T is
           the opening t_j = (j + 1/6)/e of the largest flank (k = 1), else proposes nothing (k = 0).
  WINDOW:  the openings inside the longest component of the lonely set L of the four smaller elements.
  EARLY:   the earliest opening of the largest flank lying in L (k = 1) -- equals j* iff j* is the first.
Reports hits, the expected hits sum(k/e), and the ratio."""
import math
from fractions import Fraction as F
rows = [tuple(map(int, l.split())) for l in open("six_tight_dump_v1_100.txt")]
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def cascade(S, n=6, cap=10000):
    t = F(1, n * min(S))
    for _ in range(cap):
        blk = [d for d in S if cd(d * t) < F(1, n)]
        if not blk: return t
        nxt = []
        for d in blk:
            x = d * t - F(1, n); c = -((-x.numerator) // x.denominator)
            nxt.append((c + F(1, n)) / d)
        t = max([t] + nxt)
    return None
def lonely_set(R):
    ivs = [(F(0), F(1))]
    for p in R:
        bands = [(F(6*k + 1, 6*p), F(6*k + 5, 6*p)) for k in range(p)]
        ivs = [(max(a, c), min(b, d)) for a, b in ivs for c, d in bands if max(a, c) <= min(b, d)]
    return sorted(ivs)
res = {"CASCADE": [0, 0.0], "WINDOW": [0, 0.0], "EARLY": [0, 0.0]}
for a, b, c, d, e, js in rows:
    S = (a, b, c, d, e)
    T = cascade(S)
    # T is an opening of e iff e*T - 1/6 is an integer; reduce mod 1 period
    x = e * T - F(1, 6)
    k_c = 1 if x.denominator == 1 else 0
    if k_c:
        jc = int(x) % e
        res["CASCADE"][0] += jc == js
    res["CASCADE"][1] += k_c / e
    L = lonely_set((a, b, c, d))
    longest = max(L, key=lambda iv: iv[1] - iv[0])
    W = [j for j in range(e) if longest[0] <= F(6*j+1, 6*e) <= longest[1]]
    res["WINDOW"][0] += js in W; res["WINDOW"][1] += len(W) / e
    res["EARLY"][0] += 1; res["EARLY"][1] += 1 / e  # j* is the only opening in L, so EARLY always hits
for k, (h, ex) in res.items():
    print(f"{k:8s}: hits {h}/{len(rows)}; expected by chance {ex:.2f}; ratio {h/ex if ex else float('nan'):.2f}")
