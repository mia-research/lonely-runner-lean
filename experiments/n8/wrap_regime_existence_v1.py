"""Existence at the global start in the regime section 4.6's claim actually covers.

Section 4.6: at t = 1/(8*mu), every SPEED gap reads a_k/(8*mu) >= 1/8. Those readings are
position differences mod 1, so the claim needs the whole spread inside one lap: W <= 8*mu.
Then the seven speed gaps use at least 7/8 of the lap and the ONLY gap that can be short is
the wrap gap joining r_8 back to r_1.

  W <= 7*mu      : forces all seven gaps = mu -- the progression       [PROVED, arithmetic]
  7*mu < W <= 8*mu: 'exactly six runners are lonely there, the short pair being (r_1, r_8)'
                    [VERIFIED -- 35 of 35 in the manuscript]

That is the owner's circle point as an EXISTENCE statement: in this regime Existence is
already discharged for six of the eight runners at a single named instant, and the entire
remaining obligation is the wrap pair finding a mutual scale.

Generated here on purpose: gaps a_1..a_7 each in [mu, 2*mu] with sum <= 8*mu.
"""
import random
from fractions import Fraction as F

def cyclic_gaps(V, t):
    pos = sorted((((v * t) % 1.0), i) for i, v in enumerate(V))
    m = len(pos); out = []
    for k in range(m):
        p, i = pos[k]; pn, j = pos[(k + 1) % m]
        out.append(((pn - p) if k < m - 1 else (pn + 1.0 - p), i, j))
    return out

rng = random.Random(20260917)
D = 10000
arrs = []
tries = 0
while len(arrs) < 4000 and tries < 400000:
    tries += 1
    mu_n = rng.randint(200, 1200)
    gaps = [F(rng.randint(mu_n, 2 * mu_n), D) for _ in range(7)]
    mu = min(gaps)
    if sum(gaps) > 8 * mu:            # keep only W <= 8*mu
        continue
    V = [F(0)]
    for g in gaps: V.append(V[-1] + g)
    V = [v + F(1) for v in V]          # shift off zero; differences unchanged
    arrs.append((V, mu, sum(gaps)))

reg7 = reg8 = 0
six_lonely = 0; wrap_is_short = 0; one_short = 0
lonely_hist = {}
for V, mu, W in arrs:
    b = W / mu
    if b <= 7: reg7 += 1
    else: reg8 += 1
    t = F(1, 8) / mu
    g = cyclic_gaps([float(v) for v in V], float(t))
    short = [(gg, i, j) for gg, i, j in g if gg < 1/8 - 1e-9]
    flank = set()
    for gg, i, j in short: flank.add(i); flank.add(j)
    nl = 8 - len(flank)
    lonely_hist[nl] = lonely_hist.get(nl, 0) + 1
    if len(short) == 1:
        one_short += 1
        _, i, j = short[0]
        if {i, j} == {0, 7}: wrap_is_short += 1
    if nl == 6: six_lonely += 1

n = len(arrs)
print(f"arrangements generated with W <= 8*mu   : {n}")
print(f"  of which W <= 7*mu (the progression)  : {reg7}")
print(f"  of which 7*mu < W <= 8*mu             : {reg8}")
print()
print(f"exactly ONE short gap at the global start : {one_short}  ({100*one_short/n:.1f}%)")
print(f"  ...and it is the WRAP pair (r_1, r_8)   : {wrap_is_short}  "
      f"({100*wrap_is_short/max(one_short,1):.1f}% of those)")
print(f"exactly SIX runners lonely at that instant: {six_lonely}  ({100*six_lonely/n:.1f}%)")
print()
print("runners lonely at the global start:")
for k in sorted(lonely_hist):
    print(f"   {k} lonely: {lonely_hist[k]:>5}  ({100*lonely_hist[k]/n:.1f}%)")
