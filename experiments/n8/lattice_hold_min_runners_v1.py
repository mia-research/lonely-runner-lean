"""W3 at one lattice. Instants u = p/8, p = 1..P (all integers, the full lattice). A runner with reading s (slot residue
c = floor(s) mod 8, deviation e) is in the way at p iff p·s is within 1 of a multiple of 8 (strict). Depth: distance of s from
the nearest multiple of 8. For P and a depth floor eta, the fewest runners with depth >= eta whose in-the-way instants together
include every p = 1..P. Exact rationals; depth-first search on the lowest instant not yet in the way, maximal patterns only,
capped at 8 runners (reported '>7' if eight do not suffice... i.e. if seven do not)."""
from fractions import Fraction as F
import math, sys
def masks_for(P, eta):
    out = {}
    for c in range(8):
        bps = {F(0), F(1)}
        for p in range(1, P + 1):
            for K in range((p * c - 1) // 8 - 1, (p * c + p + 1) // 8 + 2):
                for edge in (8 * K - 1, 8 * K + 1):
                    x = F(edge - p * c, p)
                    if 0 < x < 1: bps.add(x)
        for edge in (eta, 1 - eta):
            if 0 < edge < 1: bps.add(F(edge))
        bps = sorted(bps)
        for a, b in zip(bps, bps[1:]):
            e = (a + b) / 2; s = c + e
            depth = min(s % 8, 8 - s % 8)
            if depth < eta: continue
            m = 0
            for p in range(1, P + 1):
                v = p * s; k = round(v / 8)
                if abs(v - 8 * k) < 1: m |= 1 << (p - 1)
            if m and m not in out: out[m] = (c, a, b)
    ms = sorted(out, key=lambda x: -bin(x).count('1'))
    keep = []
    for m in ms:
        if not any((m | k) == k for k in keep): keep.append(m)
    return keep, out
def fewest(P, masks, cap=7):
    full = (1 << P) - 1
    by_bit = [[m for m in masks if m >> i & 1] for i in range(P)]
    best = [cap + 1]; wit = [None]
    def dfs(u, k, chosen):
        if u == full:
            if k < best[0]: best[0] = k; wit[0] = list(chosen)
            return
        if k + 1 >= best[0]: return
        i = (~u & full).bit_length() - 1 if False else next(j for j in range(P) if not u >> j & 1)
        for m in by_bit[i]:
            chosen.append(m); dfs(u | m, k + 1, chosen); chosen.pop()
    dfs(0, 0, [])
    return best[0], wit[0]
for P in (8, 12, 16, 20, 24):
    row = [f'P={P:2d}']
    for eta in (F(0), F(1, 16), F(1, 8), F(1, 4), F(1, 2)):
        masks, info = masks_for(P, eta)
        k, w = fewest(P, masks)
        row.append(f'eta={str(eta):4s}: {k if k <= 7 else ">7"}')
    print('  '.join(row)); sys.stdout.flush()

# witnesses at P = 24, eta = 1/2: which readings (slot residue + deviation piece) hold every p/8, p <= 24, in the way
masks, info = masks_for(24, F(1, 2))
k, w = fewest(24, masks)
print(f'witness at P=24, eta=1/2 ({k} runners):')
for m in w:
    c, a, b = info[m]
    print(f'   reading in ({c + a}, {c + b}) = ({float(c + a):.4f}, {float(c + b):.4f}); in the way at p = {[p for p in range(1, 25) if m >> (p - 1) & 1]}')
