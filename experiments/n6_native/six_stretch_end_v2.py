#!/usr/bin/env python3
"""E33 v2: both orientations, exact values.
(+1) piece dies at r's exit = J0; takeover on r's next lap needs 5/6 - rho_q > d_q/(3 d_r), rho_q = q's reading at J0.
(-1) piece dies at r's entry = J1; takeover on r's previous lap needs sigma_p - 1/6 > d_p/(3 d_r), sigma_p = p's
     reading at J1 (p = J's latest entry).
Reports: the inequality (strict / equality / fails) with the takeover's status from the tsv (open/born); exact top
values of rho_q and sigma_p with the speed ratio d_q/d_r or d_p/d_r alongside; and who q (or p) is relative to r.
Usage: six_stretch_end_v2.py file.tsv"""
import sys, ast
from fractions import Fraction as F
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
def frac(z): return z - (z.numerator // z.denominator)
res = Counter(); vals = {1: Counter(), -1: Counter()}; who = Counter()
for row in rows:
    d = ast.literal_eval(row[6]); nz = [(i + 1, v) for i, v in enumerate(d) if v]
    if len(nz) != 1 or abs(nz[0][1]) != 1: continue
    r, s = nz[0]
    S = ast.literal_eval(row[0][row[0].index("("):]); m = int(row[1]); x = F(row[2]); L = ast.literal_eval(row[3])
    W = [F(S[i]) if i + 1 > m else F(S[0] * (i + 1)) for i in range(5)]; W[m - 1] = x
    others = [i for i in range(1, 6) if i != r]
    ent = {i: (6 * L[i-1] + 1) / (6 * W[i-1]) for i in others}; ext = {i: (6 * L[i-1] + 5) / (6 * W[i-1]) for i in others}
    J0, J1 = max(ent.values()), min(ext.values())
    p = [i for i in others if ent[i] == J0][0]; q = [i for i in others if ext[i] == J1][0]; dr = W[r-1]
    if s == 1:
        val = frac(W[q-1] * J0); lhs, rhs = F(5, 6) - val, W[q-1] / (3 * dr); key = (val, W[q-1] / dr); other = q
    else:
        val = frac(W[p-1] * J1); lhs, rhs = val - F(1, 6), W[p-1] / (3 * dr); key = (val, W[p-1] / dr); other = p
    res[(s, "strict" if lhs > rhs else ("equality" if lhs == rhs else "fails"), row[10])] += 1
    vals[s][key] += 1
    who[(s, "binding runner slower than r" if W[other-1] < dr else "binding runner faster than r")] += 1
print("inequality by orientation and takeover status:", dict(sorted(res.items())))
print("binding runner vs r:", dict(who))
for s in (1, -1):
    print(f"orientation {s:+d}: commonest (reading, binding speed / d_r):")
    for (v, rt), c in vals[s].most_common(10): print(f"   {c:5d}  reading {v} = {float(v):.4f}, ratio {rt} = {float(rt):.4f}")
