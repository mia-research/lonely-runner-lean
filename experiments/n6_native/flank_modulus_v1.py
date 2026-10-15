#!/usr/bin/env python3
"""E48: neighbours and bystanders by the flank's own modulus. SixResidual in [1,40]. Isolations: every lonely opening
(b, k), k < b, of every set (certificate: e <= d(6k+1) mod 6b <= 5b for all d), and separately the cascade's ending.
At an opening the flank b reads exactly 1/6 (residue b). Other runners d: residue R = d(6k+1) mod 6b, reading R/6b.
Neighbours: the exit neighbour (largest reading) and the entry-side neighbour other than the flank (least reading
among d != b); the rest are bystanders. Classes: gcd(d, b) = 1 (unit of Z/b) or > 1 (zero divisor of Z/b), and
gcd(d, 6b). Also whether a neighbour's residue is exactly at an edge (b or 5b), and R/b rounded (where in the band)."""
from math import gcd
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
def cls(d, b): return "unit mod b" if gcd(d, b) == 1 else "zero divisor mod b"
stats = {}
def rec(tag, S, b, k):
    m = 6 * k + 1
    R = {d: d * m % (6 * b) for d in S if d != b}
    ex = max(R, key=lambda d: R[d]); en = min(R, key=lambda d: R[d])
    st = stats.setdefault(tag, {x: Counter() for x in ("exit", "entry2", "byst", "base", "g6", "edge", "pos")})
    st["exit"][cls(ex, b)] += 1; st["entry2"][cls(en, b)] += 1
    for d in R:
        st["base"][cls(d, b)] += 1
        if d not in (ex, en): st["byst"][cls(d, b)] += 1
    st["g6"][(gcd(ex, 6 * b) // gcd(ex, b), gcd(en, 6 * b) // gcd(en, b))] += 1
    st["edge"][(R[en] == b, R[ex] == 5 * b)] += 1
    st["pos"][(round(R[en] / b, 1), round(R[ex] / b, 1))] += 1
for r in rows:
    S = eval(r[0]); T = r[5]
    num, den = map(int, T.split("/")) if "/" in T else (int(T), 1)
    # cascade ending: T = (6k+1)/(6b) for the flank b with b*T - 1/6 an integer
    for b in S:
        if (6 * b * num) % den == 0 and ((6 * b * num) // den - 1) % 6 == 0:
            rec("cascade ending", S, b, ((6 * b * num) // den - 1) // 6); break
    for b in S:
        for k in range(b):
            m = 6 * k + 1
            if all(b <= d * m % (6 * b) <= 5 * b for d in S): rec("all lonely openings", S, b, k)
for tag, st in stats.items():
    print(f"== {tag}:")
    for part in ("base", "exit", "entry2", "byst"):
        t = sum(st[part].values()); print(f"   {part:6s}", {k: round(v / t, 3) for k, v in st[part].items()}, f"(n = {t})")
    print("   extra factor gcd(d,6b)/gcd(d,b) of (exit, entry2):", st["g6"].most_common(6))
    print("   neighbours on the edge (entry2 at b, exit at 5b):", dict(st["edge"]))
    print("   (entry2, exit) residue / b, top:", st["pos"].most_common(6))
