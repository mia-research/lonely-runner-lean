"""E222 (2026-10-01): the Level B catalogue checked (docs/n8/CASCADE_ACCOUNT_LEVEL_B_v1.md, B.12).

Owner: "Yes we are not looking at lean until the map is complete" (Level B approved in the same message).  M8: every item
is derived; this run checks the derivations, pass condition 0 failures on every item.  Exact; the cascade is
`e151_block_v1.trace` (BSM, strict).  Positions p = 8*s*t.  A reading in slot l exits at (8l+1)/(8s) and entered at
(8l-1)/(8s).  Items B1-B10; B.8's conveyor breaks classified by kind; edge cases counted.
Populations: every 7-set of readings <= 20; 1,000 seeded fine shapes; the 5,400 late band shapes (check only).
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8


def inway(d, t):
    return cd(d * t) < E8


def slot(d, t):
    return round(d * t)          # p = 8dt in (8l-1, 8l+1)  <=>  dt within 1/8 of l


def exit_of(d, t):
    l = slot(d, t); return F(8 * l + 1, 8 * d)


def entry_of(d, t):
    l = slot(d, t); return F(8 * l - 1, 8 * d)


def check(S):
    S = tuple(sorted(S)); m = S[0]
    ts, moves = trace(S)
    fail = Counter(); rec = Counter()
    if moves:   # B10
        t0, way0, st0, nx0 = moves[0]
        ex = {c: exit_of(c, t0) for c in way0}
        mx = max(ex.values())
        if set(st0) != {c for c in way0 if ex[c] == mx} or nx0 != mx:
            fail['B10'] += 1
    for j, (t, way, st, nx) in enumerate(moves):
        D = nx - t
        nxt = moves[j + 1] if j + 1 < len(moves) else None
        # B1
        ex = {c: exit_of(c, t) for c in way}
        mx = max(ex.values())
        if nx != mx or set(st) != {c for c in way if ex[c] == mx}:
            fail['B1'] += 1
        Cn = {r for r in S if inway(r, nx)}
        for a in st:
            k = (8 * a * nx - 1) / 8
            if k.denominator != 1:
                fail['lap not whole'] += 1; continue
            k = int(k)
            # B2
            for b in S:
                pos = F(b * (8 * k + 1), a)
                l = round(pos / 8)
                ins = a * (8 * l - 1) < b * (8 * k + 1) < a * (8 * l + 1)
                if ins != inway(b, nx):
                    fail['B2'] += 1
            # B3
            run = {b for b in S if b < a and (k == 0 or a * (8 * k - 1) < b * (8 * k + 1))}
            slotk_slower = {b for b in S if b < a and inway(b, nx) and slot(b, nx) == k}
            if run != slotk_slower:
                fail['B3 run'] += 1
            for b in S:
                if b < a and b not in run and not (8 * b * nx <= 8 * k - 1):
                    fail['B3 below run'] += 1
            if nxt is None:
                if run:
                    fail['B5 landing not a cluster bottom'] += 1
                continue
            stn = nxt[2]
            sweeps = [b for b in stn if b < a and slot(b, nx) == k]
            if sweeps:
                rec['sweep'] += 1
                if min(run) not in sweeps or any(b != min(run) for b in sweeps):
                    fail['B4 sweep to the run bottom'] += 1
            else:
                rec['bridge up' if all(b > a for b in stn) else 'bridge down or mixed'] += 1
                if run and not max(exit_of(b, nx) for b in stn) > F(8 * k + 1, 8 * min(run)):
                    fail['B5-B6 passage end'] += 1
        # B7-B8: queue and conveyor
        clear = [q for q in S if q not in way]
        T = {}
        for q in clear:
            p = 8 * q * t
            T[q] = (8 * math.floor(p / 8) + 7 - p) / (8 * q)
        if not clear:
            continue
        tmin = min(T.values()); front = {q for q in clear if T[q] == tmin}
        if nxt is None:
            # B9
            rec['landing: no arrival' if tmin >= D else 'landing: front passed through'] += 1
            if Cn:
                fail['B9'] += 1
            continue
        stn = set(nxt[2])
        conveyor = bool(front & stn)
        exn = {r: exit_of(r, nx) for r in Cn}
        mxn = max(exn.values())
        derived = any(f in Cn and exn[f] >= mxn for f in front)
        if conveyor != derived:
            fail['B8 conveyor condition'] += 1
        rec['conveyor holds' if conveyor else 'conveyor breaks'] += 1
        fC = [f for f in front if f in Cn]
        for f in fC:
            for r in Cn:
                if r != f and r not in way and r < f:
                    lag = entry_of(r, nx) - entry_of(f, nx)
                    if lag >= 0 and not exn[r] > exn[f]:
                        fail['B8 slower arrival outlasts'] += 1
                    if lag < 0:
                        rec['edge: arrival entered before the front (front lapped)'] += 1
        if not conveyor:
            kinds = set()
            if not fC:
                kinds.add('front not in next crowd')
            for f in fC:
                for r in Cn:
                    if r == f or exn[r] <= exn[f]:
                        continue
                    if r in way:
                        kinds.add('re-entry outlasts')
                    elif r < f:
                        kinds.add('slower arrival')
                    else:
                        kinds.add('faster arrival entering late')
            if not kinds:
                fail['B8 unclassified break'] += 1
            for kd in kinds:
                rec['break: ' + kd] += 1
    return fail, rec


def run(sets):
    Fa = Counter(); Ra = Counter()
    for S in sets:
        f, r = check(S); Fa.update(f); Ra.update(r)
    return Fa, Ra


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
    out = open('cascade_level_b_check_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    pops = [('every 7-set of readings <= 20', list(itertools.combinations(range(1, 21), 7))),
            ('1,000 seeded fine shapes, spread uniform in [2, 20]', fine(221, 1000, 2, 20)),
            ('the 5,400 late band shapes', late_shapes())]
    with Pool(8) as pool:
        for name, sets in pops:
            res = pool.map(run, [sets[i::64] for i in range(64)])
            Fa = Counter(); Ra = Counter()
            for f, r in res:
                Fa.update(f); Ra.update(r)
            w("\n== %s: %d sets ==" % (name, len(sets)))
            w("  FAILURES by item (pass: none): %s" % (dict(Fa) if Fa else 'none'))
            w("  records (not failures): %s" % dict(sorted(Ra.items())))
    out.close()
    print(open('cascade_level_b_check_v1.out').read()[len(__doc__):])
