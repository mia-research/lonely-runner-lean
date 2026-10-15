#!/usr/bin/env python3
"""E51: BHK §7 sets (bhk_case = S7 in six_cascade_observe_v1.tsv; 3 v1 < v3, D = v3 - v2 divides neither v1 nor
v3) against the window steps. Over one period of each set, the J123 windows (runners 1-3 all clear):
 (a) BHK's route (Corollary 5): a full 3-gap that is also a 123-gap (a J123 window equal to a whole clear lap of
     runner 3, length 2/(3 v3)); exists?
 (b) a J123 window of length >= 2/(3 v4) (BHK Lemma 4 / window_two_uniform);
 (c) a J123 window of length >= L(rho)/v4, rho = v5/v4 (window_two, sharp);
 (d) for sets with none of these: the exact two-window test (six_safe_exact_v1), pairs within one period, up to
     three windows apart.
Prints counts and the leftover sets."""
import math, sys
from fractions import Fraction as F
from collections import Counter
E = {}; exec(open("six_safe_exact_v1.py").read().split('if __name__ == "__main__":')[0], E)
safe_exact = E["safe_exact"]
s6, s56 = F(1, 6), F(5, 6)
def clear_ivs(d, a, b):
    out = []; k = math.floor(a * d - s56)
    while (6*k+1) / (6*d) <= b:
        lo, hi = max(a, (6*k+1)/(6*d)), min(b, (6*k+5)/(6*d))
        if lo < hi: out.append((lo, hi))
        k += 1
    return out
def Lform(rho):
    m = max(-(-(rho + 1) // 3) - 1, 0)
    return max(F(1, 3) + 1 / (3 * rho), (m + F(1, 3)) / rho)
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
c = Counter(); left = []; two = Counter(); n = 0
for r in rows:
    if r[1] != "S7": continue
    S = [F(x) for x in eval(r[0])]; n += 1
    g = math.gcd(*[int(x) for x in S]); P = F(1, g)
    ivs = [(F(0), 2 * P)]
    for d in S[:3]: ivs = [iv for a, b in ivs for iv in clear_ivs(d, a, b)]
    W = [w for w in ivs if w[0] < P]
    full3 = any(b - a == F(2, 3) / S[2] for a, b in W)
    lw = max((b - a for a, b in W), default=F(0))
    rho = S[4] / S[3]
    a_, b_, c_ = full3, lw >= F(2, 3) / S[3], lw >= Lform(rho) / S[3]
    c[(("full 3-gap" if a_ else "-"), (">= 2/(3v4)" if b_ else "-"), (">= L/v4" if c_ else "-"))] += 1
    if c_: continue
    found = False
    for i in range(len(W)):
        for j in range(i + 1, min(i + 4, len(W) + 2)):
            a1, b1 = W[i]; a3, b3 = W[j % len(W)]
            if j >= len(W): a3, b3 = a3 + P, b3 + P
            ok, _ = safe_exact(S[3]*(b1 - a1), S[3]*(a3 - b1), S[3]*(b3 - a3), rho)
            if ok: found = True; break
        if found: break
    two["SAFE pair" if found else "none"] += 1
    if not found: left.append(tuple(int(x) for x in S))
print(f"§7 sets: {n}")
print("(full 3-gap that is a 123-gap, longest J123 >= 2/(3v4), >= L(rho)/v4):")
for k, v in c.most_common(): print("  ", v, k)
print("sets without a single long-enough window, two-window exact test:", dict(two))
print("leftover sets:", left[:30], "..." if len(left) > 30 else "")
