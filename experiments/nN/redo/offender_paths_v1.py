"""The offending runner moved continuously through the cascade (E110 follow-up; E104's method, wider).  Exact.

Sets (readings of the slowest runner of (c, c + d_1, ...), 1..24):
  A: the 201 double collisions no single move rescues (two readings = 0 mod 8); offenders = the two colliders;
  B: the 8 other sets no single move rescues; offenders = every reading blocking some L0 numerator;
  C: 300 edge pushes (fixed seed sample of exceptions rescued by moving a sole blocker); offenders = the sole blockers.
Path: offender d -> d + s, s = i/32, -32 <= i <= 32, skipping coincidences.  At each s the cascade from the bound
(1/(8 d_min) of the moved set) gives t*, the setter e (the runner exactly on 1/8) and its lap K.

Recorded per path: the segments of constant (setter identity, K); whether the setter is the moved runner; the setter's
eighth-slot at the bound and at the L0 instant it was blocked on (unperturbed); and the base landing's setter's role."""
import ast, random
from fractions import Fraction as F
from math import floor
from collections import Counter
from lattice_vs_cascade_v1 import nd, E8, clear_js, live
from lattice_exceptions_v1 import rows, blockers, L0_of

def cascade(T):
    t = F(1, 8 * min(T))
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)

def setter(T, t):
    for i, d in enumerate(T):
        x = d * t - E8
        if x.denominator == 1: return i, int(x)
        x = d * t + E8
        if x.denominator == 1: return i, -int(x)      # a runner exactly at 7/8 (behind); lap recorded negative
    return None, None

def slot(x): return int(floor(8 * (x % 1)))

def rescued_by_one(T, L0):
    for i, d in enumerate(T):
        for s in (-2, -1, 1, 2):
            d2 = d + s
            if d2 <= 0 or d2 in T: continue
            T2 = tuple(sorted(T[:i] + (d2,) + T[i + 1:]))
            if clear_js(T2, L0_of(T2)): return True
    return False

A, B, Cpool = [], [], []
for (k, T, L0, Ds, e, K) in rows:
    if rescued_by_one(T, L0): Cpool.append((T, L0)); continue
    (A if sum(1 for d in T if d % 8 == 0) == 2 else B).append((T, L0))
C = random.Random(110).sample(Cpool, 300)

def offenders(T, L0, kind):
    Bk = blockers(T, L0)
    if kind == 'A': return [d for d in T if d % 8 == 0]
    if kind == 'B': return sorted({d for b in Bk for d in b})
    return sorted({b[0] for b in Bk if len(b) == 1})

S = [F(i, 32) for i in range(-32, 33)]
stats = {k: Counter() for k in 'ABC'}; examples = {k: [] for k in 'ABC'}
for kind, sets in (('A', A), ('B', B), ('C', C)):
    st = stats[kind]
    for T, L0 in sets:
        t0 = cascade(T); i0, K0 = setter(T, t0); e0 = T[i0]
        bound = F(1, 8 * T[0])
        st['sets'] += 1
        st[('base setter slot at the bound', slot(e0 * bound))] += 1
        for d in offenders(T, L0, kind):
            idx = T.index(d); segs = []; prev = None
            for s in S:
                d2 = d + s
                if d2 <= 0 or any(d2 == x for j, x in enumerate(T) if j != idx): continue
                T2 = T[:idx] + (d2,) + T[idx + 1:]
                t = cascade(T2); i, K = setter(T2, t)
                key = (i, K)
                if key != prev: segs.append([s, s, i, K, t]); prev = key
                else: segs[-1][1] = s
            st['paths'] += 1
            st[('segments on the path', min(len(segs), 9))] += 1
            base = next(sg for sg in segs if sg[0] <= 0 <= sg[1])
            st['base segment: setter is the moved runner'] += (base[2] == idx)
            # which runner sets the isolation in each segment: the moved runner, the base setter, or another
            for sg in segs:
                who = 'moved' if sg[2] == idx else ('base setter' if sg[2] == i0 else 'other')
                st[('segment setter', who)] += 1
                slt = slot(T[sg[2]] * bound) if sg[2] != idx else 'moved'
                st[('segment setter slot at the bound (unmoved runners)', slt)] += 1
            if len(examples[kind]) < 6:
                examples[kind].append((T, d, [(str(a), str(b), T[i] if i != idx else f'moved {d}', K, str(t)) for a, b, i, K, t in segs]))

for kind in 'ABC':
    print(f"=== {kind}")
    for k_, v in sorted(stats[kind].items(), key=str): print("  ", k_, v)
    for T, d, segs in examples[kind]:
        print(f"   {T}, moving {d}:")
        for sg in segs: print("      s in [", sg[0], ",", sg[1], "] setter", sg[2], "lap", sg[3], "t*", sg[4])
