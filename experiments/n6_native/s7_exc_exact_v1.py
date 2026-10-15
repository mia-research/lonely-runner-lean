#!/usr/bin/env python3
"""E51: exact rechecks for s7_exceptional_v1_80.out. (1) TIEONLY sets: recompute the meeting-time windows exactly and
test W >= L(rho)/v4. (2) RELAXED FAILS sets: any J123 window in one period of length >= L(rho)/v4 (not only at
meeting times); if none, the exact two-window test (six_safe_exact_v1), pairs up to three apart."""
import math
from fractions import Fraction as F
from collections import Counter
E = {}; exec(open("six_safe_exact_v1.py").read().split('if __name__ == "__main__":')[0], E); safe_exact = E["safe_exact"]
s6, s56 = F(1, 6), F(5, 6)
def frac(z): return z - (z.numerator // z.denominator)
def Lform(rho):
    m = max(-(-(rho + 1) // 3) - 1, 0)
    return max(F(1, 3) + 1 / (3 * rho), (m + F(1, 3)) / rho)
def clear_ivs(d, a, b):
    out = []; k = math.floor(a * d - s56)
    while (6*k+1) / (6*d) <= b:
        lo, hi = max(a, (6*k+1)/(6*d)), min(b, (6*k+5)/(6*d))
        if lo < hi: out.append((lo, hi))
        k += 1
    return out
tie, fail = [], []
for line in open("s7_exceptional_v1_80.out"):
    if line.startswith("TIEONLY"): tie.append(tuple(map(int, line.split()[1:6])))
    if line.startswith("RELAXED FAILS"): fail.append(tuple(map(int, line.split()[2:7])))
ok_tie = 0
for S0 in tie:
    S = [F(x) for x in S0]; D = S0[2] - S0[1]; L = Lform(S[4] / S[3]) / S[3]; good = False
    for k in range(1, D + 1):
        t = F(k, D); lo, hi, okk = F(-10**9), F(10**9), True
        for d in S[:3]:
            x = frac(d * t)
            if not (s6 <= x <= s56): okk = False; break
            lo = max(lo, t - (x - s6) / d); hi = min(hi, t + (s56 - x) / d)
        if okk and hi - lo >= L: good = True; break
    ok_tie += good
print(f"tie-only sets: {len(tie)}; exactly >= L: {ok_tie}")
c = Counter(); left = []
for S0 in fail:
    S = [F(x) for x in S0]; P = F(1, math.gcd(*S0)); rho = S[4] / S[3]
    ivs = [(F(0), 2 * P)]
    for d in S[:3]: ivs = [iv for a, b in ivs for iv in clear_ivs(d, a, b)]
    W = [w for w in ivs if w[0] < P]
    if max((b - a for a, b in W), default=0) >= Lform(rho) / S[3]: c["single window (off the meeting times)"] += 1; continue
    found = False
    for i in range(len(W)):
        for j in range(i + 1, min(i + 4, len(W) + 2)):
            a1, b1 = W[i]; a3, b3 = W[j % len(W)]
            if j >= len(W): a3, b3 = a3 + P, b3 + P
            if safe_exact(S[3]*(b1 - a1), S[3]*(a3 - b1), S[3]*(b3 - a3), rho)[0]: found = True; break
        if found: break
    c["two windows SAFE" if found else "neither"] += 1
    if not found: left.append(S0)
print(f"relaxed-fail sets: {len(fail)}:", dict(c))
print("neither:", left[:20], len(left))
