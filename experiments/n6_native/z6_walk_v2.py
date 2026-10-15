#!/usr/bin/env python3
"""Observation only; follow-up to z6_walk_v1. Same sets and walk.
(1) Setter and in-the-way rates per runner of each class (normalised by how many runners of that class exist).
(2) At the final instant T: for each shift u = 1..5, the share of sets with T + u/6 lonely, by the set's counts of
    E (2,4 mod 6), T (3), M (0) runners; and the identity used: runner d is unmoved by u/6 iff 6 | d u
    (M: all u; E: u = 3; T: u = 2, 4; U: none).
(3) At T, the reading (in twelfths) of each class: where units and zero divisors sit when the cascade stops."""
from fractions import Fraction as F
from collections import Counter, defaultdict
exec(open("z6_walk_v1.py").read().split("first_free =")[0])
pres = Counter(); sett = Counter(); inw = Counter(); shift = defaultdict(lambda: [0] * 6); nkey = Counter()
read = defaultdict(Counter); unmoved_ok = 0; unmoved_n = 0
for S in rows:
    inst, st, iw = walk(S); T = inst[-1]
    for d in S: pres[cls(d)] += 1
    for s in st: sett[s] += 1
    for w in iw:
        for c in w: inw[c] += 1
    cnt = Counter(cls(d) for d in S); key = f"E{cnt['E']} T{cnt['T']} M{cnt['M']}"; nkey[key] += 1
    for u in range(1, 6):
        if lonely_ := all(cd(d * (T + u * SIX)) >= SIX for d in S): shift[key][u] += 1
        for d in S:
            unmoved_n += 1
            same = ((d * (T + u * SIX)) - (d * T)).denominator == 1
            unmoved_ok += same == ((d * u) % 6 == 0)
    for d in S: read[cls(d)][int(12 * ((d * T) % 1))] += 1
print(f"(identity check) unmoved by u/6 iff 6 | d u: {unmoved_ok} of {unmoved_n}")
print("(1) runners present by class:", dict(pres))
print("    setter rate per runner:", {c: round(sett[c] / pres[c], 3) for c in pres})
print("    in-the-way rate per runner:", {c: round(inw[c] / pres[c], 3) for c in pres})
print("(2) share of sets with T + u/6 lonely, u = 1..5, by class counts (E, T, M):")
for key in sorted(nkey, key=lambda k: -nkey[k])[:14]:
    print(f"    {key} ({nkey[key]}): " + "  ".join(f"u={u}:{shift[key][u] / nkey[key]:.2f}" for u in range(1, 6)))
print("(3) readings at T in twelfths (0 = [0,1/12)), by class:")
for c in ("U", "E", "T", "M"):
    tot = sum(read[c].values()); print(f"    {c}: " + " ".join(f"{k}:{read[c][k] / tot:.3f}" for k in range(12)))
