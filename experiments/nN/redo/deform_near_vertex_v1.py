"""E382 (2026-10-05), deform_near_vertex_v1: the isolation followed along E178's deformation from the AP to targets that
approach the extremal closure vertex of the tree (J=2 cell 109535 of terminals5_J2.pkl: pins 9 rho5 = 47 rho1, 15 rho3 = 47,
rho7 = 2209/297, landing sup 26433/2209).

Owner: "ok test that" (the near-vertex test proposed after Lean `IncomingWindowN`; universal transfer reduces, per E182, to
finitely many events along every path, and accumulation of events is the scenario).

CLASS: targets x(lam) = x0 + lam (v - x0) on the segment from the cell's exact interior point x0 (`near_vertex_x0_v1.txt`,
landing 11.5924846...) to its vertex v (closure; at v itself the cascade lands at 1.21, a different cell).  Inside the
cell the landing is 89/rho7, so it increases to 26433/2209 as lam -> 1.
WHAT IS RECORDED (a map run; no pass condition, no rate): per target, the exact landing at s = 1; the events along
the path s in [0,1] (E178's follow, exact bisection to 1e-12, grid NGRID); for each death after s = 0 the E182 case (1: b's
exit, 2: earlier, 3: later) and the landing after it; the sorted event parameters tau; the smallest gap between
consecutive events; and the events in the last 1/10 and 1/100 of the path.  Clustering of events as lam -> 1 would be the
accumulation scenario; no clustering is evidence for these paths only.
Exact (Fractions) throughout; floats only in printed R values.
"""
import sys, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
import deform_pinch_v1 as D
from quantity_tests_v1 import cd, E8, next_opening

NGRID = int(sys.argv[1]) if len(sys.argv) > 1 else 400
D.NGRID = NGRID
DELTA = F(1, 10 ** 15)
_orig = D.classify


def classify_k(x, sa, ka, sb, kb):
    rec = _orig(x, sa, ka, sb, kb)
    rec['ka'], rec['kb'] = ka, kb
    return rec


D.classify = classify_k


def load_x0():
    out = []
    for line in open('near_vertex_x0_v1.txt'):
        n, d = line.split('/')
        out.append(F(int(n), int(d)))
    return out


V = [F(1), F(16715503, 7123545), F(47, 15), F(726761, 173745), F(47, 9), F(15463, 2673), F(2209, 297)]


def target(lam):
    x0 = load_x0()
    return [a + lam * (b - a) for a, b in zip(x0, V)]


def shape(rho):
    return [F(7) * r / rho[-1] for r in rho]


def case_of(x, e):
    tau, t0, k = e['tau'], e['t0'], e['ka']
    d0 = D.readings_at(x, tau)
    pos = [d * t0 - math.floor(d * t0) for d in d0]
    a = pos.index(E8); b = pos.index(F(7, 8))
    ds = D.readings_at(x, tau + DELTA)
    ta = F(8 * k[a] + 1, 8) / ds[a]
    Tb = F(8 * (k[b] + 1) + 1, 8) / ds[b]
    land = D.components(ds, need=1)[0][0]
    if land < ta:
        c = 2
    elif land < Tb:
        c = 'between'
    elif land == Tb:
        c = 1
    else:
        c = 3
    return c, float(8 * min(ds) * land)


def run(args):
    name, lam = args
    rho = target(lam)
    x = shape(rho)
    S = None
    grid = [F(j, NGRID) for j in range(NGRID + 1)]
    ks = []
    bad = 0
    for j, s in enumerate(grid):
        ds = D.readings_at(x, s)
        comps = D.components(ds, need=1)
        ks.append(D.laps(ds, comps[0][0]))
        if j % 10 == 0 and D.cascade_landing(ds) != comps[0][0]:
            bad += 1
    ev = []
    for j in range(NGRID):
        D.events(x, grid[j], ks[j], grid[j + 1], ks[j + 1], ev)
    ds1 = D.readings_at(x, F(1))
    land1 = D.cascade_landing(ds1)
    rows = []
    for e in ev:
        if e.get('tau') is None:
            rows.append(dict(kind=e['kind'], tau=None)); continue
        r = dict(kind=e['kind'], tau=e['tau'], simple=e.get('simple'), protected=e.get('protected'))
        if e['kind'] == 'death' and e['tau'] != 0 and e.get('simple'):
            r['case'], r['R_after'] = case_of(x, e)
        rows.append(r)
    return dict(name=name, lam=lam, land=float(8 * min(ds1) * land1), land_exact=8 * min(ds1) * land1,
                oracle_bad=bad, rows=rows)


def report(res, out):
    for r in res:
        rows = r['rows']
        taus = sorted(x['tau'] for x in rows if x['tau'] is not None)
        gaps = [b - a for a, b in zip(taus, taus[1:]) if b > a]
        out.write("\n== %s  lam=%s  landing at s=1: %.9f (exact %s)  oracle violations %d ==\n" % (
            r['name'], r['lam'], r['land'], r['land_exact'], r['oracle_bad']))
        kinds = Counter(x['kind'] for x in rows)
        out.write("  events %d  %s  simple %d multi %d  unprotected after s=0: %d\n" % (
            len(rows), dict(kinds), sum(1 for x in rows if x.get('simple') is True),
            sum(1 for x in rows if x.get('simple') is False),
            sum(1 for x in rows if x['tau'] not in (None, 0) and x.get('protected') is False)))
        cs = Counter(x.get('case') for x in rows if 'case' in x)
        out.write("  death cases (simple, after s=0): %s\n" % dict(cs))
        out.write("  events in last 1/10 of s: %d, last 1/100: %d, last 1/1000: %d; smallest gap between events %s (%.3e)\n" % (
            sum(1 for t in taus if t > F(9, 10)), sum(1 for t in taus if t > F(99, 100)),
            sum(1 for t in taus if t > F(999, 1000)), min(gaps) if gaps else None, float(min(gaps)) if gaps else 0))
        out.write("  event parameters tau: %s\n" % [round(float(t), 6) for t in taus])
        out.write("  landings after each simple death (R): %s\n" % [x['R_after'] for x in rows if 'R_after' in x])
        out.flush()


if __name__ == '__main__':
    lams = [F(0), F(1, 2), F(9, 10), F(99, 100), F(999, 1000), F(9999, 10000), F(1) - F(1, 10 ** 6), F(1) - F(1, 10 ** 8)]
    jobs = [("lam%d" % i, l) for i, l in enumerate(lams)]
    out = open('deform_near_vertex_v1_N%d.out' % NGRID, 'w')
    out.write(__doc__ + "\n")
    with Pool(4) as pool:
        res = pool.map(run, jobs)
    report(res, out)
    out.close()
    print(open('deform_near_vertex_v1_N%d.out' % NGRID).read()[len(__doc__):])
