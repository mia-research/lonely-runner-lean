#!/usr/bin/env python3
"""Observation only. Renault 2004's order-six dispatch (taken from Chen's Lean formalisation, Research07/LRC6,
a SECONDARY source until the paper is read) laid over the cascade on primitive SixResidual, max <= 40.
Renault class: m3 = number of multiples of 3; if m3 = 1 that one is the multiple of 6 (the anchor) and the class is
the folded residues (+-1 or +-2 mod 6) of the other four: 'P5.4' (all +-1), 'P6.6' (one +-2), 'P4.1' (two +-2).
Also recorded: m2 (evens), m6 (multiples of 6).
Cascade (exact Fractions, from 1/(6 v1)): final instant T, final flank.
At T: anchor reading (when m6 = 1); whether the non-anchor runners are clear at 1/5 (Renault's order-five seed);
how many sixth shifts T + a/6 (a = 1..5) and scalings l*T (l = 2..5) are also lonely (Renault's moves);
whether the final flank is a multiple of 6 / 3 / 2."""
from fractions import Fraction as F
from collections import Counter, defaultdict
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def lonely(S, t, q=F(1, 6)): return all(cd(d * t) >= q for d in S)
def walk(S):
    t = F(1, 6 * S[0]); path = []
    while True:
        blk = [d for d in S if cd(d * t) < F(1, 6)]
        if not blk: return path, t
        best = None
        for d in blk:
            N = round(d * t); o = F(6 * N + 1, 6 * d)
            if best is None or o > best[0]: best = (o, d, N)
        t = best[0]; path.append(best[1])
def rclass(S):
    m3 = sum(d % 3 == 0 for d in S); m2 = sum(d % 2 == 0 for d in S); m6 = sum(d % 6 == 0 for d in S)
    if m3 == 1 and m6 == 1:
        pm2 = sum(d % 6 in (2, 4) for d in S if d % 6)
        c = {0: "P5.4", 1: "P6.6", 2: "P4.1"}.get(pm2, f"pm2={pm2}")
    else:
        c = {2: "P3.1", 3: "L2.3"}.get(m3, f"m3={m3}")
    return c, m3, m2, m6
feat = defaultdict(lambda: defaultdict(Counter)); size = Counter()
for S in rows:
    c, m3, m2, m6 = rclass(S); size[c] += 1
    path, T = walk(S)
    ff = path[-1] if path else S[0]
    f = feat[c]
    f["(m3,m2,m6)"][(m3, m2, m6)] += 1
    f["final flank divisible by"][("6" if ff % 6 == 0 else "3" if ff % 3 == 0 else "2" if ff % 2 == 0 else "unit")] += 1
    f["moves"][min(len(path), 4)] += 1
    if m6 == 1:
        a = [d for d in S if d % 6 == 0][0]; others = [d for d in S if d != a]
        f["anchor reading at T, sixths"][int(6 * ((a * T) % 1))] += 1
        f["others clear at 1/5 at T"][lonely(others, T, F(1, 5))] += 1
        f["others clear at 1/5 at some T+a/6"][any(lonely(others, T + F(k, 6), F(1, 5)) for k in range(6))] += 1
    f["# a in 1..5 with T+a/6 lonely"][sum(lonely(S, T + F(k, 6)) for k in range(1, 6))] += 1
    f["# l in 2..5 with l*T lonely"][sum(lonely(S, l * T) for l in range(2, 6))] += 1
print(f"primitive SixResidual sets: {len(rows)}; Renault classes: {dict(size)}")
for c in sorted(size):
    print(f"== {c} ({size[c]})")
    for k, v in feat[c].items(): print(f"   {k}: " + ", ".join(f"{x}:{n}" for x, n in sorted(v.items(), key=lambda z: -z[1])))
