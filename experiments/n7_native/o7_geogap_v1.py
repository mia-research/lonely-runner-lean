#!/usr/bin/env python3
"""Geometric-window property of five-runner blocks (EXACT Fractions): for real (rational) speeds y (min 1), the lonely
set L(y) at 1/7 on s in [0, S]; report the largest ratio L_{i+1}/U_i over consecutive components after the first, and
the first lonely instant L_1.  Claim R <=> L(y) meets [a, 6a] for all a >= a0, i.e. ratio < 6 past a0 and L_1 <= 6 a0.
Families: random y in [1, rho]^5; near-resonant y = Q/Q1 + eps (Q small integer pattern, eps rational small)."""
import math, random, sys
from fractions import Fraction as Fr
from collections import Counter
from o7_exact import inter
S7, S67 = Fr(1, 7), Fr(6, 7)
def lonely(y, S):
    cur = None
    for x in y:
        B = []; m = 0
        while (m + S7) / x <= S:
            B.append(((m + S7) / x, min((m + S67) / x, S))); m += 1
        cur = B if cur is None else inter(cur, B, strict=False)
        if not cur: return []
    return cur
def worst_ratio(y, S):
    iv = lonely(y, S)
    if not iv: return None, None
    r = max((iv[i + 1][0] / iv[i][1] for i in range(len(iv) - 1)), default=Fr(1))
    return iv[0][0], r
rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2)
S = Fr(int(sys.argv[2]) if len(sys.argv) > 2 else 120)
stats = Counter(); worst = []
for fam in ("random", "resonant"):
    for _ in range(400):
        if fam == "random":
            y = [Fr(1)] + sorted(Fr(rnd.randint(10**4 + 1, 5 * 10**4), 10**4) for _ in range(4))
        else:
            Q = sorted(rnd.sample(range(1, 10), 5)); eps = [Fr(rnd.randint(0, 300), 10**5) for _ in range(5)]
            y = sorted(Fr(q, Q[0]) + e for q, e in zip(Q, eps)); y = [x / y[0] for x in y]
        if len(set(y)) < 5: continue
        L1, r = worst_ratio(y, S)
        if r is None: stats[(fam, "no lonely on [0,S]")] += 1; continue
        stats[(fam, "ratio<6" if r < 6 else "ratio>=6")] += 1
        worst.append((float(r), float(L1), fam, [float(x) for x in y]))
worst.sort(reverse=True)
print(f"five-runner blocks, lonely set on s in [0, {S}]:", dict(stats))
print("   largest gap ratios L_(i+1)/U_i:", [(round(r, 3), round(l1, 3), f, [round(x, 4) for x in y]) for r, l1, f, y in worst[:8]])
print("   largest first lonely instant L_1:", sorted(((round(l1, 3), f) for r, l1, f, y in worst), reverse=True)[:5])
