#!/usr/bin/env python3
"""E47 (b): neighbours and bystanders at isolation instants of SixResidual sets in [1,40]. At a lonely instant t every
runner reads x_d = frac(d t) in [1/6, 5/6]; the neighbours are the runner with the least x (nearest the subject on the
entry side) and the one with the largest x (exit side); the others are bystanders. Classified by d mod 6: unit
(1, 5), zero divisor (2, 3, 4), multiple (0). Instants: the cascade's ending T (first lonely instant), and the first
lonely lap-point instant K/F + k/6 (E42) when there is one. Baseline: the mix of all runners of residual sets.
Also: is a neighbour exactly at an edge (1/6 or 5/6), and the residue pair (entry neighbour, exit neighbour)."""
from fractions import Fraction as Fr
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
def frac(z): return z - (z.numerator // z.denominator)
def kind(d): s = d % 6; return "unit" if s in (1, 5) else ("mult" if s == 0 else "zd")
base = Counter(); stats = {}
def record(tag, S, t):
    x = {d: frac(d * t) for d in S}
    assert all(Fr(1, 6) <= v <= Fr(5, 6) for v in x.values())
    lo = min(S, key=lambda d: x[d]); hi = max(S, key=lambda d: x[d])
    st = stats.setdefault(tag, {"entry": Counter(), "exit": Counter(), "byst": Counter(), "pair": Counter(), "edge": Counter(), "res": Counter()})
    st["entry"][kind(lo)] += 1; st["exit"][kind(hi)] += 1
    for d in S:
        if d not in (lo, hi): st["byst"][kind(d)] += 1
    st["pair"][(kind(lo), kind(hi))] += 1
    st["edge"][(x[lo] == Fr(1, 6), x[hi] == Fr(5, 6))] += 1
    st["res"][(lo % 6, hi % 6)] += 1
for r in rows:
    S = eval(r[0]); T = Fr(r[5])
    for d in S: base[kind(d)] += 1
    record("cascade ending T", S, T)
    F = max(S); done = False
    for K in range(F):
        for k in range(1, 6):
            t = Fr(K, F) + Fr(k, 6)
            if all(Fr(1, 6) <= frac(d * t) <= Fr(5, 6) for d in S):
                record("first lonely lap-point instant", S, t); done = True; break
        if done: break
tot = sum(base.values())
print("baseline, all runners of residual sets:", {k: round(v / tot, 3) for k, v in base.items()})
for tag, st in stats.items():
    print(f"== {tag}:")
    for part in ("entry", "exit", "byst"):
        t = sum(st[part].values()); print(f"   {part:5s}: ", {k: round(v / t, 3) for k, v in st[part].most_common()}, f"(n = {t})")
    print("   (entry, exit) kinds:", st["pair"].most_common(6))
    print("   neighbours exactly at the edges (entry at 1/6, exit at 5/6):", dict(st["edge"]))
    print("   (entry, exit) residues mod 6, top:", st["res"].most_common(8))
