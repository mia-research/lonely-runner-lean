#!/usr/bin/env python3
"""E51: §7 at the meeting times tau_k = k/D (D = v3 - v2; runners 2, 3 coincide). For each k < D: the J123 window
containing tau_k (runners 1-3 clear), its length; BHK's route needs it to be a full 3-gap (P, Corollary 5);
the sharp window needs length >= L(rho)/v4. Per set: does some meeting time satisfy BHK's requirement; the relaxed one;
for sets where BHK's main route fails at every meeting time (the exceptional orbits), what does the relaxed route
give, and what is the orbit (n = number of distinct meeting points, the step (c3, c1) = (v3 mod D, v1 mod D))."""
import math
from fractions import Fraction as F
from collections import Counter
s6, s56 = F(1, 6), F(5, 6)
def frac(z): return z - (z.numerator // z.denominator)
def Lform(rho):
    m = max(-(-(rho + 1) // 3) - 1, 0)
    return max(F(1, 3) + 1 / (3 * rho), (m + F(1, 3)) / rho)
def window_at(S, t):
    """J123 window containing t (all of runners 1..3 clear around t), or None if one is blocked at t."""
    lo, hi = F(-10**9), F(10**9)
    for d in S[:3]:
        x = frac(d * t)
        if not (s6 <= x <= s56): return None
        lo = max(lo, t - (x - s6) / d); hi = min(hi, t + (s56 - x) / d)
    return lo, hi
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
res = Counter(); exc = []; exc_rel = Counter(); n_tot = 0
for r in rows:
    if r[1] != "S7": continue
    S = [F(x) for x in eval(r[0])]; n_tot += 1
    v1, v2, v3, v4, v5 = [int(x) for x in S]; D = v3 - v2
    L = Lform(S[4] / S[3]) / S[3]
    bhk = rel = False
    for k in range(1, D + 1):
        t = F(k, D); w = window_at(S, t)
        if w is None: continue
        full = (w[1] - w[0]) == F(2, 3) / S[2]
        bhk |= full; rel |= (w[1] - w[0]) >= L
    res[("BHK main route" if bhk else "-", "relaxed (sharp window)" if rel else "-")] += 1
    if not bhk:
        pts = {(v3 * k % D, v1 * k % D) for k in range(D)}
        exc.append((v1, v2, v3, v4, v5)); exc_rel[("relaxed works" if rel else "relaxed fails", f"n={len(pts)}")] += 1
print(f"§7 sets: {n_tot}")
print("meeting-time routes:", dict(res))
print("sets where BHK's main route fails (exceptional orbits):", len(exc))
print("  relaxed route there, by orbit size n:", dict(sorted(exc_rel.items())))
print("  examples:", exc[:20])
