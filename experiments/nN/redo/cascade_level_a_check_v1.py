"""E221 (2026-10-01): the Level A catalogue checked (docs/n8/CASCADE_ACCOUNT_LEVEL_A_v1.md, A.13).

Owner: "yes approved, start with the Level A catalogue".  M8: every item is derived; this run checks the derivations,
with pass condition 0 failures on every item.  Exact arithmetic; the cascade is `e151_block_v1.trace` (BSM: in the way iff
circDist < 1/8, strict); the clear set is computed without the cascade (`band_cert_v1/core.clear_set`).
Positions p = 8*d*t (eighths of a lap).  Items: A1, A2, A3, A4-A5, A6, A7, A8, A10, with A11's edge cases counted.
Populations: every 7-set of readings <= 20; 1,000 seeded fine shapes (least 1,000, spread uniform in [2, 20]); the
5,400 late band shapes (a record population, used only as a check).
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8


def inway(d, t):
    return cd(d * t) < E8


def check(S):
    S = tuple(sorted(S)); m = S[0]; s = [F(d, m) for d in S]
    ts, moves = trace(S)
    fail = Counter(); edge = Counter()
    # A10: the first crowd is the captures
    caps = {d for d in S if (F(d, m) % 8) > 7 or (F(d, m) % 8) < 1}
    first = set(moves[0][1]) if moves else set()
    if caps != first:
        fail['A10'] += 1
    for i, (t, way, st, nx) in enumerate(moves):
        D = nx - t
        last = (i == len(moves) - 1)
        # A1
        if not nx > t:
            fail['A1 advance'] += 1
        cs = clear_set(s, 8 * m * t, 8 * m * nx)
        if last:
            if not cs or cs[0][0] != 8 * m * nx:
                fail['A1 landing least'] += 1
        elif cs:
            fail['A1 no lonely inside'] += 1
        # A2: the new instant is (8K+1)/(8h) for a setter h
        ok2 = False
        for h in st:
            q = 8 * h * nx - 1
            if q.denominator == 1 and q % 8 == 0 and q >= 0:
                ok2 = True
        if not ok2:
            fail['A2'] += 1
        # A3: setter attains max (1 - x_c)/(8c), and D equals it
        rem = {}
        for c in way:
            p = 8 * c * t
            x = p - 8 * round(p / 8)
            rem[c] = (1 - x) / (8 * c)
        mx = max(rem.values())
        if D != mx or set(st) != {c for c in way if rem[c] == mx}:
            fail['A3'] += 1
        if len(st) > 1:
            edge['tied setters'] += 1
        # A4-A5: next crowd by the rotation formula, split into arrivals and re-entries
        nxt_formula = set()
        for r in S:
            pr = 8 * r * t + 8 * r * D
            y = pr % 8
            if y > 7 or y < 1:
                nxt_formula.add(r)
        nxt_test = {r for r in S if inway(r, nx)}
        if nxt_formula != nxt_test:
            fail['A4-A5 formula'] += 1
        arrivals = {r for r in nxt_test if r not in way}
        reentries = {r for r in nxt_test if r in way}
        for c in reentries:
            p = 8 * c * t; x = p - 8 * round(p / 8)
            if not D > (7 - x) / (8 * c):
                fail['A5 re-entry condition'] += 1
        edge['re-entries'] += len(reentries)
        # A7: setters clear at their own exit, exactly on the edge
        for a in st:
            if cd(a * nx) != E8:
                fail['A7'] += 1
        # A6: every reading in the next crowd against each setter
        for a in st:
            ka = (8 * a * nx - 1) / 8
            for b in nxt_test:
                pb = 8 * b * nx
                l = round(pb / 8)
                if b > a and not l > ka:
                    fail['A6 faster later lap'] += 1
                if b < a and not l <= ka:
                    fail['A6 slower same or earlier lap'] += 1
                if b < a and l == ka and not a * (8 * ka - 1) < b * (8 * ka + 1):
                    fail['A6 sweep ratio'] += 1
        # A11: readings other than setters exactly on an edge at the new instant
        for r in S:
            if r in st:
                continue
            y = (8 * r * nx) % 8
            if y == 1 or y == 7:
                edge['reading exactly on an edge'] += 1
    # A8: the landing's certificate
    if moves:
        h = min(moves[-1][2]); K8 = 8 * h * ts - 1; K = K8 / 8
    else:
        h = m; K = F(0)
    if 8 * h * ts != 8 * K + 1 or K.denominator != 1:
        fail['A8 setter edge'] += 1
    for d in S:
        if d != h:
            y = (8 * d * ts) % 8
            if not (1 <= y <= 7):
                fail['A8 block'] += 1
    if K == 0:
        if h != m:
            fail['A8 K=0 slowest'] += 1
    else:
        below = [d for d in S if d < h]
        if below:
            d = max(below)
            if not h * (8 * K - 1) >= d * (8 * K + 1):
                fail['A8 cluster'] += 1
    return fail, edge, len(moves)


def run(sets):
    F_ = Counter(); E_ = Counter(); L = Counter()
    for S in sets:
        f, e, n = check(S)
        F_.update(f); E_.update(e); L[n] += 1
    return F_, E_, L


def fine(seed, n, lo, hi):
    r = random.Random(seed); out = []
    while len(out) < n:
        m = 1000; W = int(r.uniform(lo, hi) * m)
        S = tuple(sorted({m, W} | {r.randrange(m + 1, W) for _ in range(5)}))
        if len(S) == 7:
            out.append(S)
    return out


if __name__ == '__main__':
    sys.path.insert(0, '.')
    from coverB_fine_v1 import late_shapes
    out = open('cascade_level_a_check_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    pops = [('every 7-set of readings <= 20', list(itertools.combinations(range(1, 21), 7))),
            ('1,000 seeded fine shapes, spread uniform in [2, 20]', fine(221, 1000, 2, 20)),
            ('the 5,400 late band shapes', late_shapes())]
    with Pool(8) as pool:
        for name, sets in pops:
            chunks = [sets[i::64] for i in range(64)]
            res = pool.map(run, chunks)
            Fa = Counter(); Ea = Counter(); La = Counter()
            for f, e, l in res:
                Fa.update(f); Ea.update(e); La.update(l)
            w("\n== %s: %d sets, %d moves ==" % (name, len(sets), sum(k * v for k, v in La.items())))
            w("  FAILURES by item (pass: none): %s" % (dict(Fa) if Fa else 'none'))
            w("  A11 edge cases counted (not failures): %s" % dict(Ea))
            w("  chain lengths (moves): %s" % dict(sorted(La.items())))
    out.close()
    print(open('cascade_level_a_check_v1.out').read()[len(__doc__):])
