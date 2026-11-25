"""v7: as v6, printing every end with sigma = +1, form T, or a crossing-side state R >= 7 that is not the gate entry.
v6: as v5, and each solved end's relation recorded: form, the frozen reading j's rank, the laps m and m', the edge sigma,
  the state R at the end written exactly as (8m+1)/r_s in units R = 8t, and whether the end is the gate itself
  (form B with j = rank 1, m' = 1, sigma = -1: the moved reading's exit at exactly R = 7, reading 1's zone entry).
v5: as v2, and each island end solved EXACTLY.
  At the divergent move p the state is t_p = (8m+1)/(8 r_s) (setter s, lap m) or t0 = 1/8.  The cascade's decisions there are
  (a) blocked(r_c, t_p): r_c t_p against m' -/+ 1/8, and (b) the max-exit comparison (8m+1)/r_c against (8m''+1)/r_d.
  Each is an equation in two speeds (or one speed and t0).  With only r_k varying, the end is where one equation that
  involves r_k becomes an equality.  v5 takes the reading c whose status differs across the end (or, for 'swapped', the two
  readings whose exits tie), writes the equation, solves it for r_k = v*, and checks: a <= v* <= b (the bisection bracket,
  width (hi - lo) 2^-90 or less), and which side v* itself belongs to (gate(v*)).
  Relation forms (j a frozen reading, m, m' laps, sigma = -1 entering, +1 leaving):
    A   state set by j, k changes status:      r_k = (8m' + sigma) r_j / (8m + 1)
    A0  state t0 = 1/8, k changes status:      r_k = 8m' + sigma
    B   state set by k, j changes status:      r_k = (8m + 1) r_j / (8m' + sigma)
    T   exits of k and j tie:                  r_k = (8m + 1) r_j / (8m' + 1)
    F   neither s nor c is k (no equation in r_k at move p): reported, not solved.
v2: as v1, with each end sorted by how the in-the-way set at t_p changes across the end:
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
            ra = sorted(six + [a]); rb = sorted(six + [b])
            Ta, pa, sa, ea = run(ra); Tb, pb, sb, eb = run(rb)
            q = ev['p']; t = sa[q]; s_ = ea[q]          # setter index in ra (None = t0)
            def rk_of(rr): return rr.index(a) if rr is ra else rr.index(b)
            ka = ra.index(a)
            def frozen_val(i): return ra[i]             # frozen readings are the same on both sides
            sol = None; form = None; rel = None
            if kind == 'swapped':
                ex = sorted(((nxt(ra[u - 1], t), u - 1) for u in A_), reverse=True)
                (e1, u1), (e2, u2) = ex[0], ex[1]
                j = u2 if u1 == ka else u1
                if ka in (u1, u2):
                    m = ceil(a * t - E); m2 = ceil(ra[j] * t - E)
                    sol = (8 * m + 1) * ra[j] / (8 * m2 + 1); form = 'T'; rel = (j + 1, m, m2, 1)
                else: form = 'F'
            else:
                diff = sorted(A_ ^ B_)
                cidx = diff[0] - 1
                if len(diff) != 1: form = 'F'
                else:
                    xr = ra[cidx] * t; mp = round(xr); sig = 1 if xr - mp > 0 else -1
                    if abs(abs(xr - mp) - E) > Fr(1, 10**6): form = 'F'
                    elif cidx == ka:
                        if s_ is None: sol = Fr(8 * mp + sig); form = 'A0'; rel = (None, 0, mp, sig)
                        else:
                            m = ra[s_] * t - E; assert m.denominator == 1
                            sol = (8 * mp + sig) * ra[s_] / (8 * m + 1); form = 'A'; rel = (s_ + 1, int(m), mp, sig)
                    elif s_ == ka:
                        m = a * t - E; assert m.denominator == 1
                        sol = (8 * m + 1) * ra[cidx] / (8 * mp + sig); form = 'B'; rel = (cidx + 1, int(m), mp, sig)
                    else: form = 'F'
            c[('exact', kind, 'form', form)] += 1
            if rel is not None:
                jr, m_, mp_, sg = rel
                c[('relation', form, 'j', jr, 'm', m_, "m'", mp_, 'sigma', sg)] += 1
                c[('relation', form, 'j', jr)] += 1
                c[('relation', 'gate entry (B, j = 1, m\' = 1, sigma = -1)', form == 'B' and jr == 1 and mp_ == 1 and sg == -1)] += 1
                c[('relation', 'crossing-side state R below 7', 8 * t < 7, 'gate entry', form == 'B' and jr == 1 and mp_ == 1 and sg == -1)] += 1
                ge = form == 'B' and jr == 1 and mp_ == 1 and sg == -1
                if sg == 1 or form == 'T' or (8 * t >= 7 and not ge):
                    print('RARE | E340 index', idx, '| moved reading', k + 1, side, kind, '| form', form, 'j', jr, 'm', m_, "m'", mp_, 'sigma', sg, '| state R = %s ~ %.12f' % (8 * t, float(8 * t)), '| in the way crossing', sorted(A_), 'other', sorted(B_), '| setter rank', None if s_ is None else s_ + 1, '| solved r_k ~ %.12f' % float(sol), '| readings (floats, steer only)', [round(float(x), 6) for x in ra])
            if sol is not None:
                inside = min(a, b) <= sol <= max(a, b)
                c[('exact', 'solution in the bracket', inside)] += 1
                if inside:
                    c[('exact', 'the solved point crosses the gate', g(sol))] += 1
                else:
                    print('OUTSIDE', idx, k + 1, side, kind, form, float(sol), float(a), float(b))
            else:
                print('UNSOLVED', idx, k + 1, side, kind, form, sorted(A_), sorted(B_), s_, ka)
            c[('end change', kind, 'type', ev['typ'], 'crossing-side blockers', len(A_))] += 1
            c[('end type', ev['typ'], 'moved reading changes status' if ev['moved_changes'] else 'a frozen reading changes status')] += 1
            c[('end', 'non-crossing side lands at that state', ev['lands_there'])] += 1
            c[('end', 'readings in the way on the crossing side', len(ev['ina']))] += 1
            c[('end', 'state R below 7', ev['R'] < 7)] += 1
            if mode == 'first':
                print('k = %d %s end at %.12f (float, steer only): move %d, state R = %s ~ %.6f, set by rank %s | type %s | in the way: crossing side %s, other side %s | other side lands there: %s (R* %.6f)' % (
                    k + 1, side, float(a), ev['p'], ev['R'], float(ev['R']), ev['setter'], ev['typ'], ev['ina'], ev['inb'], ev['lands_there'], float(ev['Tb'])))
for kk, val in sorted(c.items(), key=str): print(val, '|', kk)
