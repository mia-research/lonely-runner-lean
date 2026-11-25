"""v2: as v1, with each end sorted by how the in-the-way set at t_p changes across the end:
  break    the crossing side has readings in the way, the other side none (the cascade lands at t_p);
  added    the other side has one more reading in the way (the maximum-exit move changes);
  swapped  the sets differ otherwise.
E948: how phase 1 sets the gate islands' ends, through the cascade (2026-11-25).  Exact Fractions.
For each crosser (or the first, mode 'first') and each reading k = 2..7 (k = 7 in (r_6, 2 r_7)), the island as in
path_islands_v2 (150 equal points + actual + pass-interval midpoints; ends bisected 90 times on the gate predicate).
At each end, with a = last crossing point, b = first non-crossing point: the first move p at which the two paths
differ, the state t_p there (R = 8 t_p), and:
  type B  t_p is set by the moved reading (its exit moves with it) and a frozen reading changes its in-the-way status;
  type A  the moved reading itself changes its in-the-way status at t_p, a state set by a frozen reading (or t0);
  the readings in the way at t_p on the crossing side, and on the other side;
  whether the non-crossing side lands at t_p (the chain breaks there: nobody in the way).
"""
import pickle, glob, sys
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('path_islands_v2.py').read().split("step = int(sys.argv[1])")[0])
def run(rs):
    T, path = cascade(rs, E); t = E; st = [t]; setter = [None]
    for p in path:
        lap = floor(p * t + E); t = (lap + E) / p; st.append(t); setter.append(rs.index(p))
    return T, path, st, setter
def end_event(six, k, a, b):
    ra = sorted(six + [a]); rb = sorted(six + [b])
    Ta, pa, sa, ea = run(ra); Tb, pb, sb, eb = run(rb)
    ia = [ra.index(x) for x in pa]; ib = [rb.index(x) for x in pb]
    p = next((u for u in range(min(len(ia), len(ib))) if ia[u] != ib[u]), min(len(ia), len(ib)))
    ta, tb = sa[p], sb[p]
    ina = tuple(q + 1 for q in range(7) if blocked(ra[q], ta)); inb = tuple(q + 1 for q in range(7) if blocked(rb[q], tb))
    typ = 'B' if ea[p] == k else 'A'
    moved_changes = ((k + 1) in ina) != ((k + 1) in inb)
    return dict(p=p, R=8 * ta, ina=ina, inb=inb, typ=typ, moved_changes=moved_changes, lands_there=(Tb == tb), Tb=8 * Tb, setter=None if ea[p] is None else ea[p] + 1)
mode = sys.argv[1]
if mode == 'first':
    todo = [r for r in rows if r[0] == 44824]; step, off = 1, 0
else:
    step, off = int(sys.argv[2]), int(sys.argv[3]); todo = rows[off::step]
c = Counter()
for idx, R0, closers, cls, att in todo:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, _ = cascade(rs, E)
    for k in range(1, 7):
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]; hi = rs[k + 1] if k < 6 else 2 * rs[6]
        ws = windows(six, E, T1); nW = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y)
        pts = [lo + (hi - lo) * Fr(i, 150) for i in range(1, 150)] + [rs[k]]
        for x, y, z in ws[:nW + 2]:
            P = passes(x, y, lo, hi, limit=5000)
            if P: pts += [(l + h) / 2 for l, h, m in P]
        pts = sorted(set(p for p in pts if lo < p < hi))
        cr = {v: 8 * cascade(sorted(six + [v]), E)[0] >= 9 for v in pts}
        ia = pts.index(rs[k]); i0 = ia
        while i0 > 0 and cr[pts[i0 - 1]]: i0 -= 1
        i1 = ia
        while i1 < len(pts) - 1 and cr[pts[i1 + 1]]: i1 += 1
        g = lambda v, six=six: gate(sorted(six + [v]))
        for side, (i, j) in (('left', (i0, i0 - 1)), ('right', (i1, i1 + 1))):
            if j < 0 or j >= len(pts): c[('end', 'segment end')] += 1; continue
            a = pts[i]; b = pts[j]
            for _ in range(90):
                m = (a + b) / 2
                if g(m): a = m
                else: b = m
            ev = end_event(six, k, a, b)
            c[('end', side, 'type', ev['typ'])] += 1
            A_, B_ = set(ev['ina']), set(ev['inb'])
            kind = 'break' if not B_ else ('added' if A_ < B_ else ('removed, others remain' if B_ < A_ else 'swapped'))
            c[('end change', kind)] += 1
            c[('end change', kind, 'type', ev['typ'], 'crossing-side blockers', len(A_))] += 1
            c[('end type', ev['typ'], 'moved reading changes status' if ev['moved_changes'] else 'a frozen reading changes status')] += 1
            c[('end', 'non-crossing side lands at that state', ev['lands_there'])] += 1
            c[('end', 'readings in the way on the crossing side', len(ev['ina']))] += 1
            c[('end', 'state R below 7', ev['R'] < 7)] += 1
            if mode == 'first':
                print('k = %d %s end at %.12f (float, steer only): move %d, state R = %s ~ %.6f, set by rank %s | type %s | in the way: crossing side %s, other side %s | other side lands there: %s (R* %.6f)' % (
                    k + 1, side, float(a), ev['p'], ev['R'], float(ev['R']), ev['setter'], ev['typ'], ev['ina'], ev['inb'], ev['lands_there'], float(ev['Tb'])))
for kk, val in sorted(c.items(), key=str): print(val, '|', kk)
