"""TOUCH TRANSPORT v2 (Task AD, finishing run).  Exact Fractions / integers only; no floats.

v2 does not change the v1 event solver (touch_transport_v1.py is imported unchanged).  It adds what v1 lacked:

  V1  an INDEPENDENT exact cell routine (different algorithm: elementary intervals between all zone edges, midpoint and
      point tests with the definition 'dist(d t, Z) >= 1/8 for every runner'), compared with v1's cells_at on random
      disparity sets including ties (shared edges), and on the AP.
  V2  hand-derivable exact cases: (a) the AP at T=1 has exactly the four degenerate cells {1/8},{3/8},{5/8},{7/8};
      (b) the path 'runner 8 from 15/2 to 9, others at the AP' (subject rank 0): a pair-law crossing at s0 = 1/3, a death at
      t = 1/8 and a birth at t = 7/8, derived by hand in the text of the .out.
  V3  label audit: for sampled paths, at several rational s inside every phase and just beside every breakpoint, the
      independent cells equal v1's phase cell list with its (opener, closer) labels evaluated at that s.
  V4  the question of an empty lonely set: at EVERY breakpoint and at 12 interior points of EVERY window-empty phase the
      exact cascade (IsMove / nextOpening) terminates, and the first lonely instant it gives is the left end of the first
      exact cell found by the independent routine in an enlarged window.  Every death with no cell left in the window
      is listed in full (all of them, not 25), with the exact next cell.
  V5  death/birth at s0 are degenerate cells at s0 (touch) -- counted; ties named.
Grades: [OBS] = data with the population stated; [reasoned] otherwise.  Counting is tagged "count".
"""
import sys, os, random
from fractions import Fraction as F
from math import floor, ceil
from multiprocessing import Pool
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import touch_transport_v1 as V1

E8 = F(1, 8)
dist_int = V1.dist_int


# ---------------------------------------------------------------- V1 independent cells
def lonely_at(ds, t):
    return t > 0 and all(dist_int(d * t) >= E8 for _, d in ds)


def indep_cells(ds, T):
    """cells of {0 < t <= T : every runner has dist(d t, Z) >= 1/8} as list of (u, w)."""
    pts = {F(0), F(T)}
    for _, d in ds:
        m = 0
        while True:
            lo = F(8 * m - 1) / (8 * d)
            if lo > T:
                break
            for e in (F(8 * m - 1) / (8 * d), F(8 * m + 1) / (8 * d)):
                if 0 < e < T:
                    pts.add(e)
            m += 1
    P = sorted(pts)
    cells = []
    cur = None
    for j in range(len(P) - 1):
        a, b = P[j], P[j + 1]
        if lonely_at(ds, (a + b) / 2):
            assert lonely_at(ds, b) and (a == 0 or lonely_at(ds, a))
            if cur is None:
                cur = [a, b]
            else:
                cur[1] = b
        else:
            if cur is not None:
                cells.append(tuple(cur))
                cur = None
        if cur is None and lonely_at(ds, b):
            cur = [b, b]
    if cur is not None:
        cells.append(tuple(cur))
    return cells


def v1_cells_uw(ds, T):
    return [(c[0], c[1]) for c in V1.cells_at(ds, T)]


def test_indep_random(rng, n=3000):
    bad = 0
    for _ in range(n):
        T = rng.choice((1, 2, 3))
        kind = rng.random()
        if kind < 0.4:      # integer / simple rational disparities: many shared edges (ties)
            ds = [(i, F(rng.randint(1, 20), rng.choice((1, 2, 3, 4)))) for i in range(7)]
        elif kind < 0.7:    # near-AP
            ds = [(i, F(i + 1) + F(rng.randint(-8, 8), 100)) for i in range(7)]
        else:
            ds = [(i, F(rng.randint(1, 400), rng.randint(1, 40))) for i in range(7)]
        a = v1_cells_uw(ds, T)
        b = indep_cells(ds, T)
        if a != b:
            bad += 1
            if bad <= 3:
                print('   MISMATCH T=%d ds=%s\n      v1=%s\n      indep=%s' % (T, [d for _, d in ds], a, b))
    return n, bad


# ---------------------------------------------------------------- label evaluation of v1 cells
def eval_cell(cell, dmap, T):
    u = V1.val_open(cell[2][0], dmap)
    w = V1.val_close(cell[3][0], dmap, T)
    return (u, w)


# ---------------------------------------------------------------- per-path work
def first_cell_beyond(dvals_items, tstar):
    """independent: enlarge the window until it holds a cell, return the first cell."""
    Tbig = max(2, ceil(tstar) + 1)
    return indep_cells(dvals_items, Tbig)


def work(args):
    pid, (pop, desc, v, w), T, audit = args
    path = V1.Path(list(v), list(w))
    rng = random.Random(pid * 7919 + 13)
    out = Counter()
    rows_none = []
    mism = []
    for k in range(8):
        r = V1.analyse(path, k, T, (pid, pop, desc), keep_phases=True)
        A, B = path.coeffs(k)
        out['subject-paths'] += 1
        out['phases'] += r['phases']
        phases = r['phases_cells']
        # V3 label audit (sampled paths only)
        if audit:
            for (a, b, cells) in phases:
                pts = [a + (b - a) * x for x in (F(1, 2), F(1, 7), F(6, 7), F(1, 1000), F(999, 1000))]
                for s in pts:
                    ds = path.ds(k, s, A, B)
                    dm = dict(ds)
                    got = [eval_cell(c, dm, T) for c in cells]
                    ind = indep_cells(ds, T)
                    out['V3 points'] += 1
                    if got != ind:
                        out['V3 mismatches'] += 1
                        if len(mism) < 3:
                            mism.append((desc, k, s, got, ind))
        # V5 + death/birth degenerate at s0
        for ev in r['events']:
            s0 = ev['s0']
            for it in ev['items']:
                if it['cat'] in ('DEATH', 'BIRTH') and 0 < s0 < 1:
                    out['%s items' % it['cat']] += 1
                    if it['u'] != it['w']:
                        out['%s at nondegenerate cell at s0' % it['cat']] += 1
                    out['%s: kinds %s' % (it['cat'], ','.join(it['kinds']))] += 1
        # V4 emptiness
        br = sorted(set([F(0), F(1)] + [e['s0'] for e in r['events']]))
        for s0 in br:
            dm = path.ds(k, s0, A, B)
            ts, steps = V1.cascade_first([d for _, d in dm])
            out['V4 breakpoints cascaded'] += 1
            if ts is None:
                out['V4 cascade NOT terminated'] += 1
        for (a, b, tstar) in r['zero_window_phases']:
            out['V4 window-empty phases'] += 1
            for x in [F(j, 13) for j in range(1, 13)]:
                s = a + (b - a) * x
                ds = path.ds(k, s, A, B)
                ts, steps = V1.cascade_first([d for _, d in ds])
                out['V4 window-empty interior points cascaded'] += 1
                if ts is None or ts <= T:
                    out['V4 BAD (cascade not beyond T or not terminated)'] += 1
                    continue
                fc = first_cell_beyond(ds, ts)
                if not fc or fc[0][0] != ts:
                    out['V4 cascade != independent first cell'] += 1
        # none-left deaths (full list)
        for ev in r['events']:
            s0 = ev['s0']
            if not (0 < s0 < 1):
                continue
            for it in ev['items']:
                if it['cat'] == 'DEATH' and ev['nafter'] == 0:
                    ts = ev['tstar_after']
                    ph = [(a, b) for (a, b, c) in phases if a == s0][0]
                    s = (ph[0] + ph[1]) / 2
                    ds = path.ds(k, s, A, B)
                    fc = first_cell_beyond(ds, ts)
                    rows_none.append(dict(pop=pop, desc=desc, k=k, s0=s0, dying=(it['u'], it['nb'][0][1]),
                                          opener=it['nb'][0][2], closer=it['nb'][0][3], before=ev['before'],
                                          tstar=ts, nextcell=fc[0] if fc else None,
                                          nco=it['nco'], kinds=it['kinds']))
    return pid, dict(out), rows_none, mism


def cls(t):
    return int(round(8 * t)) % 8


def main():
    T = 1
    rng = random.Random(20261012)
    print('TOUCH TRANSPORT v2 (verification + completion of v1).  Exact Fractions only.  v1 solver imported unchanged.')
    print()
    print('V1  independent cell routine vs v1 cells_at [OBS]:')
    n, bad = test_indep_random(rng)
    print('   random disparity sets (7 disparities, ties included, T in {1,2,3}): %d compared, %d mismatches (count)' % (n, bad))
    ap = [(i, F(i)) for i in range(1, 8)]
    apc = indep_cells(ap, 1)
    print('   AP subject rank 0 (disparities 1..7), T=1: indep cells = %s ; v1 cells = %s' % (apc, v1_cells_uw(ap, 1)))
    assert apc == [(F(1, 8), F(1, 8)), (F(3, 8), F(3, 8)), (F(5, 8), F(5, 8)), (F(7, 8), F(7, 8))]
    print('   hand derivation: t=a/8 (a odd) gives d t = a d/8; the closest integer distance is >= 1/8 for d=1..7 (a=1: d=7 gives 7/8 = 1 - 1/8;')
    print('   a=3: d=3 -> 9/8, d=5 -> 15/8; mirror a -> 8-a), and t is lonely nowhere else: the open zones (0,1/8),(7/56,9/56)=(1/8,9/56) ... tile (0,1].  [reasoned + checked]')
    print()
    print('V2  hand path: subject rank 0, speeds (1,2,3,4,5,6,7,15/2) -> (1,2,3,4,5,6,7,9), s in [0,1].')
    v = [F(x) for x in (1, 2, 3, 4, 5, 6, 7)] + [F(15, 2)]
    w = [F(x) for x in (1, 2, 3, 4, 5, 6, 7)] + [F(9)]
    # sorted strictly: v_8 = 15/2 > 7.
    path = V1.Path(v, w)
    r = V1.analyse(path, 0, 1, ('hand', 'hand', 'hand'), keep_phases=True)
    print('   d_7(s) = 13/2 + 3s/2 ; d_1 = 1.  Pair law (a=1,b=7): the cell [1/(8 d_1), 7/(8 d_7)] exists iff d_7 <= 7 d_1, i.e. s <= 1/3;')
    print('   (a=7,b=1): [49/(8 d_7), 7/(8 d_1)] exists iff d_7 >= 7, i.e. s >= 1/3.  At s0=1/3 both are the points 1/8 and 7/8:')
    print('   hand prediction: DEATH at t0=1/8 and BIRTH at t0=7/8, both at s0=1/3.')
    for ev in r['events']:
        its = [it for it in ev['items'] if it['cat'] not in V1.SKIP]
        if its and 0 < ev['s0'] < 1:
            print('   s0=%s: ' % ev['s0'] + '; '.join('%s [%s,%s] opener=%s closer %s->%s' % (it['cat'], it['u'], it['w'], it['opens'],
                  [x[3] for x in it['nb']], [x[3] for x in it['na']]) for it in its))
    got = {(ev['s0'], it['cat'], it['u']) for ev in r['events'] for it in ev['items']}
    ok = (F(1, 3), 'DEATH', F(1, 8)) in got and (F(1, 3), 'BIRTH', F(7, 8)) in got
    print('   hand prediction found in the event list: %s' % ok)
    assert ok
    print('   cells in phases:')
    for (a, b, cells) in r['phases_cells']:
        print('     s in (%s,%s): %s' % (a, b, V1.fmt_cells(cells)))
    print()

    pops = V1.pop_A() + V1.pop_B() + V1.pop_P() + V1.pop_Q() + V1.pop_CX()
    audit_ids = set(i for i in range(len(pops)) if i % 4 == 0 or pops[i][0] in ('P', 'Q', 'CX'))
    print('Populations: those of v1 unchanged (same seeds): %s' % dict(Counter(p[0] for p in pops)))
    print('V3 label audit runs on %d of %d paths (every 4th path of A/B plus all of P, Q, CX), all 8 subjects, T=1.' % (len(audit_ids), len(pops)))
    tasks = [(i, p, T, i in audit_ids) for i, p in enumerate(pops)]
    with Pool() as pool:
        res = pool.map(work, tasks, chunksize=1)
    tot = Counter()
    none_rows = []
    mism = []
    for pid, out, rn, mm in res:
        tot.update(out)
        none_rows += rn
        mism += mm
    print()
    print('V3/V4/V5 totals [OBS], T=1, count over all subject-paths:')
    for k_, v_ in sorted(tot.items()):
        if k_.startswith('DEATH: kinds') or k_.startswith('BIRTH: kinds'):
            continue
        print('   %-70s %d' % (k_, v_))
    for m in mism:
        print('   V3 MISMATCH', m)
    print()
    print('V5 tie structure at DEATH/BIRTH items: the kinds of coincident zone edges at the touch point (RL = opener of one runner equals closer of another), count:')
    kc = Counter()
    for k_, v_ in tot.items():
        if k_.startswith('DEATH: kinds') or k_.startswith('BIRTH: kinds'):
            kc[k_] = v_
    for k_, v_ in kc.most_common(12):
        print('   %-60s %d' % (k_, v_))
    print()
    print('V4  DEATH with no cell left in the window (0,1] (every one, count = %d); exact data; window-free, the independent routine in an enlarged window gives the NEXT cell:' % len(none_rows))
    clsc = Counter()
    for q in none_rows:
        a = cls(q['dying'][0])
        nc = q['nextcell']
        clsc[(a, cls(nc[0]) if nc else None)] += 1
        print('   %s | rank %d | s0=%s | dying cell [%s,%s] class %d | opener(runner,lap)=%s closer=%s | cells before: %s | cascade first cell after: [%s,%s] class %d (= t* %s: %s) | ties at touch: %d %s'
              % (q['desc'], q['k'], q['s0'], q['dying'][0], q['dying'][1], a, q['opener'], q['closer'], V1.fmt_cells(q['before'] or []),
                 nc[0], nc[1], cls(nc[0]), q['tstar'], nc[0] == q['tstar'], q['nco'], q['kinds']))
    print('   (class of dying cell, class of next cell) -> count:', dict(clsc))
    print('   number with next-cell class = 8 - dying class mod 8:', sum(1 for q in none_rows if q['nextcell'] and cls(q['nextcell'][0]) == (8 - cls(q['dying'][0])) % 8))
    print()


if __name__ == '__main__':
    main()
