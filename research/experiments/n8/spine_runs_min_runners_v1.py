"""Single-scale limit. A runner with slot residue c = a mod 8 and deviation e in [0,1) is in the way at odd spine r iff
r·(c + e) is within 1 of a multiple of 8 (strict). For R0, compute every in-the-way pattern over odd r <= R0 (one per open
piece of e), and the fewest runners whose patterns together include every odd r <= R0:
  (A) any runner allowed;
  (B) no near-sharer deeper than 1/R0 (excludes c = 0 with e < 1/R0 and c = 7 with e > 1 − 1/R0);
  (C) no near-sharer at all (c in 1..6) — then spine 1 is never in the way, so spines 3..R0 only.
Exact rationals; breadth-first over unions of patterns (dominated patterns removed)."""
from fractions import Fraction as F
import math, sys
def patterns(R0, allow):
    spines = [r for r in range(1, R0 + 1, 2)]
    out = set()
    for c in range(8):
        bps = {F(0), F(1)}
        for r in spines:
            lo = r * c; hi = r * c + r
            for K in range(math.floor((lo - 1) / 8), math.ceil((hi + 1) / 8) + 1):
                for edge in (8 * K - 1, 8 * K + 1):
                    x = F(edge - r * c, r)
                    if 0 < x < 1: bps.add(x)
        bps = sorted(bps)
        for a, b in zip(bps, bps[1:]):
            e = (a + b) / 2
            if not allow(c, a, b, R0): continue
            m = 0
            for i, r in enumerate(spines):
                v = r * (c + e); k = round(v / 8)
                if abs(v - 8 * k) < 1: m |= 1 << i
            if m: out.add(m)
    # remove dominated
    ms = sorted(out, key=lambda x: -bin(x).count('1'))
    keep = []
    for m in ms:
        if not any((m | k) == k for k in keep): keep.append(m)
    return spines, keep
def fewest(spines, masks, target):
    seen = {0: 0}; frontier = [0]; k = 0
    while frontier and k < 12:
        k += 1; nxt = []
        for s in frontier:
            for m in masks:
                t = s | m
                if t not in seen:
                    seen[t] = k
                    if (t & target) == target: return k
                    nxt.append(t)
        frontier = nxt
    return None
allowA = lambda c, a, b, R0: True
allowB = lambda c, a, b, R0: not ((c == 0 and a < F(1, R0)) or (c == 7 and b > 1 - F(1, R0)))
allowC = lambda c, a, b, R0: c not in (0, 7)
for R0 in (7, 15, 23, 31):
    row = [f'R0={R0:2d}']
    for name, allow in (('A', allowA), ('B', allowB), ('C', allowC)):
        spines, masks = patterns(R0, allow)
        target = (1 << len(spines)) - 1
        if name == 'C': target &= ~1
        k = fewest(spines, masks, target)
        row.append(f'{name}: {k} ({len(masks)} patterns)')
    print('  '.join(row)); sys.stdout.flush()

# witnesses for (C): which three runners (slot residue, deviation piece) keep odd spines 3..R0 all in the way
def witnesses(R0, allow, need, limit=3):
    spines = [r for r in range(1, R0 + 1, 2)]
    items = []
    for c in range(8):
        bps = {F(0), F(1)}
        for r in spines:
            for K in range(-1, (r * 8 + r) // 8 + 2):
                for edge in (8 * K - 1, 8 * K + 1):
                    x = F(edge - r * c, r)
                    if 0 < x < 1: bps.add(x)
        bps = sorted(bps)
        for a, b in zip(bps, bps[1:]):
            if not allow(c, a, b, R0): continue
            e = (a + b) / 2; m = 0
            for i, r in enumerate(spines):
                v = r * (c + e); k = round(v / 8)
                if abs(v - 8 * k) < 1: m |= 1 << i
            if m: items.append((m, c, a, b))
    target = ((1 << len(spines)) - 1) & ~1
    import itertools
    found = []
    big = sorted(items, key=lambda x: -bin(x[0]).count('1'))[:120]
    for trio in itertools.combinations(big, need):
        u = 0
        for t in trio: u |= t[0]
        if (u & target) == target:
            found.append(trio)
            if len(found) >= limit: break
    return spines, found
for R0 in (15, 31):
    spines, found = witnesses(R0, allowC, 3)
    print(f'(C) R0={R0}: example triples (slot residue, deviation piece) keeping spines 3..{R0} in the way:')
    for trio in found:
        print('   ', ' | '.join(f'c={c} e∈({a},{b}) spines {[spines[i] for i in range(len(spines)) if m >> i & 1]}' for m, c, a, b in trio))
