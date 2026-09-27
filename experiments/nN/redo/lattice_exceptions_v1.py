"""The exceptions of lattice_vs_cascade_v1 (the first live lattice L0 does not clear), read through the cascade.  Exact.

For each exception T (readings of the slowest runner, 1..24):
  * at L0, for each numerator j the set of readings blocking (8j+1)/(8 L0): how many numerators have one blocker,
    and which runner is the sole blocker;
  * one-runner moves d -> d +- 1, d +- 2 (kept distinct, positive): does L0 (recomputed) then clear, and which runner's
    move does it;
  * the cascade's landing (e, K) and whether e is a sole blocker at L0 (the runner that sank the lattice sets the
    isolation), and the landing's position against L0: t* vs the L0 instants.
"""
import ast
from fractions import Fraction as F
from math import gcd
from collections import Counter
from lattice_vs_cascade_v1 import cascade, landing, clear_js, live, nd, E8
import itertools

def L0_of(T): return next(D for D in itertools.count(1) if live(T, D))

def blockers(T, D):
    out = []
    for j in range(D):
        t = F(8 * j + 1, 8 * D)
        out.append([d for d in T if nd(d * t) < E8])
    return out

rows = [ast.literal_eval(l) for l in open('lattice_vs_cascade_v1_exceptions.txt')]
c = Counter(); nblk = Counter(); movers = Counter(); fix = Counter()
examples = []
for (k, T, L0, Ds, e, K) in rows:
    B = blockers(T, L0)
    single = [b[0] for b in B if len(b) == 1]
    c['exceptions'] += 1
    c['every numerator singly blocked'] += (len(single) == L0)
    nblk[max(len(b) for b in B)] += 1
    c['cascade setter e is a sole blocker at L0'] += (e in single)
    c['cascade setter e blocks some numerator at L0'] += any(e in b for b in B)
    # one-runner moves
    ok = False; who = set()
    for i, d in enumerate(T):
        for s in (-2, -1, 1, 2):
            d2 = d + s
            if d2 <= 0 or d2 in T: continue
            T2 = tuple(sorted(T[:i] + (d2,) + T[i + 1:]))
            L = L0_of(T2)
            if clear_js(T2, L): ok = True; who.add(d)
    c['one move makes the first live lattice clear'] += ok
    if ok:
        c['... and the mover is the cascade setter e'] += (e in who)
        c['... and the mover is a sole blocker at L0'] += bool(who & set(single))
    if len(examples) < 8 and k >= 9: examples.append((T, L0, [tuple(b) for b in B], e, K, sorted(who)))
for k_, v in c.items(): print(f"{k_}: {v}")
print("most blockers on one numerator at L0:", sorted(nblk.items()))
print("examples (readings, L0, blockers per numerator j, cascade e, K, one-move rescuers):")
for x in examples: print("  ", x)
