#!/usr/bin/env python3
"""E47 (a): the unit / coset split at the fastest runner's lap points. SixResidual in [1,40], F = fastest. For each
K in [0, F): shifts k in Z/6 at t = K/F + k/6. Runner d: s = d mod 6, reading at K/F is x = frac(d K / F); phase
a = floor(6 x); blocks k iff (s k + a) mod 6 in {0, 5}, with exact edges (x + s k/6 exactly at 1/6 or 5/6 mod 1 is
clear). Control: rule vs direct. Per K: lonely shifts (all clear) and their class (event k in {1,5} / non-event
{2,3,4} / 0); whether E45's separation holds (events blocked only by units, non-events only by zero divisors);
for K with a lonely shift, the phases of the runners (all 0? the fastest is 0 by construction)."""
from fractions import Fraction as Fr
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open("six_cascade_observe_v1.tsv")][1:]
def frac(z): return z - (z.numerator // z.denominator)
def clear_t(d, t): f = frac(d * t); return Fr(1, 6) <= f <= Fr(5, 6)
def kind(s): return "unit" if s in (1, 5) else ("mult" if s == 0 else "zd")
ctrl = Counter(); lonely_cls = Counter(); sep = Counter(); sep_lonely = Counter(); phases0 = Counter(); n = 0; sets_hit = Counter()
for r in rows:
    S = eval(r[0]); F = max(S); n += 1; hit = False
    for K in range(F):
        blk = {}
        for d in S:
            x = frac(Fr(d * K, F)); a = int(6 * x); s = d % 6
            direct = {k for k in range(6) if not clear_t(d, Fr(K, F) + Fr(k, 6))}
            rule = set()
            for k in range(6):
                y = frac(x + Fr(s * k, 6))
                c = int(6 * y)
                if c in (0, 5) and y != Fr(5, 6): rule.add(k)
            ctrl[direct == rule] += 1
            blk[d] = (s, a, direct)
        free = [k for k in range(6) if all(k not in b[2] for b in blk.values())]
        ok = all(not (k in b[2] and kind(b[0]) != "unit") for b in blk.values() for k in (1, 5)) and \
             all(not (k in b[2] and kind(b[0]) == "unit") for b in blk.values() for k in (2, 3, 4))
        sep[ok] += 1
        if free:
            hit = True
            for k in free: lonely_cls["0" if k == 0 else ("event" if k in (1, 5) else "non-event")] += 1
            sep_lonely[ok] += 1
            phases0[sum(1 for b in blk.values() if b[1] == 0)] += 1
    sets_hit[hit] += 1
print("control (rule == direct):", dict(ctrl))
print("residual sets with a lonely lap-point shift:", dict(sets_hit))
print("lonely shifts by class:", dict(lonely_cls))
print("E45 separation at lap points, all K:", dict(sep), "; at K with a lonely shift:", dict(sep_lonely))
print("at K with a lonely shift, number of runners at phase 0 (of 5):", dict(sorted(phases0.items())))
