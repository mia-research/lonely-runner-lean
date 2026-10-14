"""Existence read in gaps (manuscript section 4.6), which is the owner's circle picture.

At time t the eight runners sit at positions v_j*t mod 1. The eight CYCLIC gaps between
consecutive positions sum to 1. So unless every gap is exactly 1/8, some gap is short
(< 1/8). Runner i is lonely at t iff NEITHER of its two adjacent gaps is short.

Section 4.6's open obligation: "the moving short gap misses both flanks of runner i at some
instant" -- i.e. runner i is not permanently flanked by a short gap.

This measures, per runner: does a short gap sit beside it at EVERY sampled instant?
"""
import random, math

def gaps_and_neighbours(V, t):
    """positions, sorted cyclically; returns for each runner the two adjacent gap widths."""
    pos = sorted(((v * t) % 1.0, i) for i, v in enumerate(V))
    m = len(pos)
    before = {}; after = {}
    for k in range(m):
        p, i = pos[k]
        pnext, _ = pos[(k + 1) % m]
        g = (pnext - p) % 1.0
        if g == 0.0: g = 1.0 if m == 1 else 0.0
        after[i] = g
        before[pos[(k + 1) % m][1]] = g
    return before, after

rng = random.Random(20260917)
SAMPLES = 4000
arrs = []
for _ in range(300):
    arrs.append(sorted(rng.uniform(1, 30) for _ in range(8)))
for _ in range(300):
    arrs.append(sorted(float(x) for x in rng.sample(range(1, 60), 8)))

always_flanked = 0
tot = 0
minshort = {}
never_lonely_cases = []
for V in arrs:
    T = max(V)
    lonely_ever = [False] * 8
    for s in range(1, SAMPLES + 1):
        t = s * (12.0 / (SAMPLES * min(V)))
        before, after = gaps_and_neighbours(V, t)
        nshort = sum(1 for i in range(8) if after[i] < 1/8)
        minshort[nshort] = minshort.get(nshort, 0) + 1
        for i in range(8):
            if before[i] >= 1/8 and after[i] >= 1/8:
                lonely_ever[i] = True
    for i in range(8):
        tot += 1
        if not lonely_ever[i]:
            always_flanked += 1
            never_lonely_cases.append((V, i))

print(f"arrangements                                  : {len(arrs)}")
print(f"(runner, arrangement) pairs                   : {tot}")
print(f"instants sampled per arrangement              : {SAMPLES}")
print()
print(f"runners NEVER free of a short flank in sampling: {always_flanked}")
print()
print("how many of the eight gaps are short (< 1/8) at an instant:")
for k in sorted(minshort):
    print(f"   {k} short : {minshort[k]:>8}  ({100*minshort[k]/sum(minshort.values()):.2f}%)")

# ---------------------------------------------------------------------------
# The 81 are suspect. The sweep above used 4,000 instants over t <= 12/min(V), which is a
# SHORT window; a null from too small a search is the failure mode this project keeps
# hitting. Re-test exactly those cases with a window 200x longer and 50x denser, and
# report whether the null survives.
print()
print("=" * 68)
print("RE-TESTING the 'never free' cases with a far larger search")
DENSE = 200000
still = []
for V, i in never_lonely_cases:
    found = None
    for s in range(1, DENSE + 1):
        t = s * (2400.0 / (DENSE * min(V)))
        before, after = gaps_and_neighbours(V, t)
        if before[i] >= 1/8 and after[i] >= 1/8:
            found = t; break
    if found is None:
        still.append((V, i))
print(f"  re-tested                    : {len(never_lonely_cases)}")
print(f"  found a lonely instant       : {len(never_lonely_cases) - len(still)}")
print(f"  STILL none                   : {len(still)}")
if still:
    print("  candidates worth exact treatment (float sampling cannot settle these):")
    for V, i in still[:5]:
        print(f"    runner {i+1} of {[round(v,4) for v in V]}")
else:
    print("  -> the 81 was a search-window artefact. Every runner sampled has an instant")
    print("     at which neither flanking gap is short, which is section 4.6's obligation")
    print("     holding in every case measured.")
