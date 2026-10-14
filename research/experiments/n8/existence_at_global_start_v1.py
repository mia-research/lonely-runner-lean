"""Existence at the global start: how much of it is already discharged there.

Owner: because it is a circle, r_8 and r_1 must eventually have a mutual scale.
Section 4.6: at the global start 1/(8*mu), mu the smallest speed gap anywhere, every SPEED
gap reads at least 1/8, so the only gap that can be short is the WRAP gap between r_8 and
r_1.  Seven gaps at >= 1/8 already use 7/8 of the lap.

If that holds, Existence is settled at the global start for every runner except the short
pair, and the whole remaining obligation is that the short pair finds a mutual scale.
Measured here: at t = 1/(8*mu), how many gaps are short and which runners are lonely.
"""
import random
from fractions import Fraction as F

def cyclic_gaps(V, t):
    """The eight cyclic gaps between positions v*t mod 1, each tagged with the pair it joins.
    They sum to 1 by construction."""
    pos = sorted((((v * t) % 1.0), i) for i, v in enumerate(V))
    m = len(pos)
    out = []
    for k in range(m):
        p, i = pos[k]
        pn, j = pos[(k + 1) % m]
        g = (pn - p) if k < m - 1 else (pn + 1.0 - p)
        out.append((g, i, j))
    return out

rng = random.Random(20260917)
arrs = []
for _ in range(400):
    arrs.append(sorted(F(x) for x in rng.sample(range(1, 200), 8)))
while len([a for a in arrs if len(a) == 8]) < 800:
    cand = sorted({F(rng.randint(1, 4000), 100) for _ in range(8)})
    if len(cand) == 8:
        arrs.append(cand)

hist_short = {}; hist_lonely = {}
wrap_is_the_short_one = 0; cases_one_short = 0
W_over_mu = {}
for V in arrs:
    mu = min(V[k+1] - V[k] for k in range(7))
    W = V[7] - V[0]
    t = F(1, 8) / mu
    g = cyclic_gaps([float(v) for v in V], float(t))
    short = [(gg, i, j) for gg, i, j in g if gg < 1/8 - 1e-12]
    hist_short[len(short)] = hist_short.get(len(short), 0) + 1
    flank = set()
    for gg, i, j in short: flank.add(i); flank.add(j)
    nl = 8 - len(flank)
    hist_lonely[nl] = hist_lonely.get(nl, 0) + 1
    if len(short) == 1:
        cases_one_short += 1
        # is the short gap the one joining the extreme speeds r_1 and r_8?
        _, i, j = short[0]
        if {i, j} == {0, 7}: wrap_is_the_short_one += 1
    b = float(W / mu)
    k = "W<=7mu" if b <= 7 else ("7mu<W<=8mu" if b <= 8 else "W>8mu")
    W_over_mu[k] = W_over_mu.get(k, 0) + 1

n = len(arrs)
print(f"arrangements                          : {n}")
print(f"spread regime  : {W_over_mu}")
print()
print("NOTE ON SCOPE. Section 4.6's claim -- that at the global start every SPEED gap reads")
print(">= 1/8 so only the wrap can be short -- needs W <= 8*mu. A speed gap reads a_k/(8*mu),")
print("which is a POSITION difference mod 1, so once W > 8*mu the readings exceed a lap, the")
print("runners have crossed, and speed-adjacency is no longer position-adjacency. Section 4.6")
print("says exactly this: 'Beyond W = 8*mu the short gap moves into the interior as runners")
print("cross.' The counts below mix both regimes and are split afterwards.")
print()
print("at the global start t = 1/(8*mu), number of SHORT gaps (<1/8):")
for k in sorted(hist_short): print(f"   {k} short : {hist_short[k]:>5}  ({100*hist_short[k]/n:.1f}%)")
print()
print("runners already LONELY at the global start (both flanks >= 1/8):")
for k in sorted(hist_lonely): print(f"   {k} lonely: {hist_lonely[k]:>5}  ({100*hist_lonely[k]/n:.1f}%)")
print()
print(f"cases with exactly one short gap      : {cases_one_short}")
print(f"  ...and it joins r_1 and r_8 (wrap)  : {wrap_is_the_short_one}")

# ---------------------------------------------------------------------------
print()
print("=" * 68)
print("SPLIT BY REGIME -- this is the distinction section 4.6 draws")
for label in ("W<=7mu", "7mu<W<=8mu", "W>8mu"):
    sub = []
    for V in arrs:
        mu = min(V[k+1] - V[k] for k in range(7)); W = V[7] - V[0]
        b = float(W / mu)
        k = "W<=7mu" if b <= 7 else ("7mu<W<=8mu" if b <= 8 else "W>8mu")
        if k != label: continue
        t = F(1, 8) / mu
        g = cyclic_gaps([float(v) for v in V], float(t))
        short = [(gg, i, j) for gg, i, j in g if gg < 1/8 - 1e-12]
        flank = set()
        for gg, i, j in short: flank.add(i); flank.add(j)
        sub.append((len(short), 8 - len(flank), {i, j} == {0, 7} if len(short) == 1 else None))
    if not sub:
        print(f"\n  {label}: none sampled"); continue
    print(f"\n  {label}: {len(sub)} arrangements")
    print(f"    short gaps at the global start, median : {sorted(s[0] for s in sub)[len(sub)//2]}")
    print(f"    runners lonely there, median           : {sorted(s[1] for s in sub)[len(sub)//2]}")
    print(f"    exactly ONE short gap                  : {sum(1 for s in sub if s[0]==1)}")
    print(f"      ...and it is the wrap pair (r1,r8)   : {sum(1 for s in sub if s[2] is True)}")
    print(f"    ZERO runners lonely at the global start: {sum(1 for s in sub if s[1]==0)}")
