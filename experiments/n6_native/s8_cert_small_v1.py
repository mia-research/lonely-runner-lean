#!/usr/bin/env python3
"""Toward a symbolic §8 proof: the smallest certificate tree we can find with the same semantics as S8CertCore_v1
(clip at every node, the E85 statement list). At each uncertified cell, candidate splits are tried in every dimension
at the points lo + k (hi - lo)/8 (k = 1..7) and, for an unbounded x5, at 6, 8, 12, 16, 24, 30; the split whose two
children certify directly is preferred, then the one with the larger certified child. Reports leaf count and the
statement regions as a list of boxes."""
import sys
from fractions import Fraction as F
sys.setrecursionlimit(100000)
exec(open("s8_cert_lean_gen_v1.py").read().split("stats = {")[0])
def cands(cc):
    lo, hi = cc; out = []
    for d in range(4):
        if hi[d] == 0:
            out += [(d, F(x)) for x in (6, 8, 12, 16, 24, 30) if x > lo[d]]
        elif hi[d] > lo[d]:
            out += [(d, lo[d] + (hi[d] - lo[d]) * k / 8) for k in range(1, 8)]
    return out
def score(cc, d, mid):
    a, b = clip(setHi(cc, d, mid)), clip(setLo(cc, d, mid))
    ca = emptyB(a) or certify(a) is not None; cb = emptyB(b) or certify(b) is not None
    def vol(c):
        lo, hi = c; v = F(1)
        for i in range(4): v *= ((hi[i] if hi[i] != 0 else F(40)) - lo[i]) if not emptyB(c) else 0
        return v
    return (ca + cb, max(vol(a) if ca else 0, vol(b) if cb else 0))
n = {"leaf": 0, "node": 0}
leaves = []
def build(c, depth):
    cc = clip(c)
    if emptyB(cc): return ("none",)
    r = certify(cc)
    if r: n["leaf"] += 1; leaves.append((cc, r)); return ("leaf", r)
    if depth > 80: raise SystemExit(f"FAIL {cc}")
    d, mid = max(cands(cc), key=lambda z: score(cc, *z))
    n["node"] += 1
    return ("node", d, mid, build(setHi(cc, d, mid), depth + 1), build(setLo(cc, d, mid), depth + 1))
root = ((F(1), F(1), F(1), F(1)), (F(3), F(3), F(6), F(0)))
tree = build(root, 0)
print("smallest-tree search:", n)
from collections import Counter
print("statements:", Counter((r[0], r[1]) for _, r in leaves).most_common())
