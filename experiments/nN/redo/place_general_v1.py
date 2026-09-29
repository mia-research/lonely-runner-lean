"""E176 (2026-09-29): the place statement of E174-E175 on larger readings and on the late band shapes.

Owner: "yes test it on larger readings and the late band shapes".

SCALE.  E174-E175's rungs a/q were instants in absolute time.  That is not scale-free: multiplying every reading by
L moves the same place to a rung with denominator Lq, and at the late band shapes' scale (nearest reading 27720) no rung
with small q exists.  Positions are what scaling keeps.  So the rung is stated here as a position of the NEAREST runner
m: the instant r = a/(q m) at which it sits at a/q of its lap.  Every reading's position there is (d/m)(a/q).  For
m = 1 this is E174-E175's rung exactly; for any m every absolute rung a/q is a nearest-runner rung with denominator
q/gcd(m, q) <= q.  So the readings <= 24 population must come out fully placed again (the positive control).

The place statement G, for the incident's left boundary t* (the cascade's landing), in this order:
  B        t* = the bound 1/(8m);
  O        t* = a reading's next opening 9/(8e);
  sep      t* = move(v) for v = B or O not lonely (one separation: the reading in the slot at v leaves);
  rung     t* = r, a rung of the nearest runner's ladder;
  rung-sep t* = move(r), r < t* not lonely (the rung displaced by one separation);
  rung-str t* = the latest opening at or before r (the stretch at the rung).
Rungs are tried in increasing q (2..QMAX); the least q that places the incident is recorded.  The slot condition is
the cascade's own: reading d is in the slot at r iff circDist(d r) < 1/8 (E175: for q <= 8 at m = 1 only multiples
of q fit; readings off the grid fit once q >= 9).

Populations: readings <= 24, all 346,104 (control); nearest reading 1 and readings <= 32, all 736,281; random seven-sets
with readings <= 48, <= 96, <= 200 (30,000 each, seed 11); the late band shapes (5,400).  Oracle check: the landing
equals the first lonely instant computed without the cascade.  Scale check: S and 3S classified alike (sample).
Misses are listed, traced, and perturbed one reading at a time through the cascade.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from quantity_tests_v1 import cd, E8, next_opening
from wave_incident_v1 import lonely_components

QMAX = 40


def lonely(T, t):
    return all(cd(d * t) >= E8 for d in T)


def move(T, t):
    way = [d for d in T if cd(d * t) < E8]
    if not way:
        return t
    return max(next_opening(d, t) for d in way)


def cascade(T):
    t = F(1, 8 * T[0]); n = 0
    while True:
        nx = move(T, t)
        if nx == t:
            return t, n
        t = nx; n += 1


def latest_opening(T, r):
    return max((math.floor(e * r - E8) + E8) / e for e in T)


def place_G(T, ts):
    m = T[0]
    B = F(1, 8 * m)
    if ts == B:
        return ('B', None)
    Os = [F(9, 8 * e) for e in T]
    if ts in Os:
        return ('O', None)
    for v in [B] + Os:
        if v < ts and not lonely(T, v) and move(T, v) == ts:
            return ('sep', None)
    pmax = m * ts + 1                      # nearest-runner positions considered, in laps
    for q in range(2, QMAX + 1):
        for a in range(1, int(pmax * q) + 1):
            if math.gcd(a, q) != 1:
                continue
            r = F(a, q * m)
            if r == ts:
                return ('rung', q)
            if r < ts:
                if not lonely(T, r) and move(T, r) == ts:
                    return ('rung-sep', q)
            elif latest_opening(T, r) == ts:
                return ('rung-str', q)
    return ('none', None)


def classify(T):
    T = tuple(sorted(T))
    ts, n = cascade(T)
    return T, ts, n, place_G(T, ts)


def with_oracle(T):
    T, ts, n, p = classify(T)
    comps = lonely_components(T, F(1, 8 * T[0]), ts + F(2, T[0]))
    return T, ts, n, p, bool(comps) and comps[0][0] == ts


def work(sets):
    return [with_oracle(T) for T in sets]


def perturb(T):
    step = max(1, T[0] // 100)
    res = []
    for i in range(7):
        for dlt in (-step, step):
            U = list(T); U[i] += dlt
            if U[i] < 1 or len(set(U)) < 7:
                continue
            U, ts, n, p = classify(U)
            res.append((i, dlt, p[0], p[1]))
    return T, res


def report(name, rows, out, pool):
    out.write("\n== %s ==  sets %d\n" % (name, len(rows)))
    out.write("oracle check (landing = independent first lonely instant): %d violations\n" % sum(not r[4] for r in rows))
    kinds = Counter(r[3][0] for r in rows)
    out.write("places: %s\n" % dict(kinds.most_common()))
    lq = Counter(r[3][1] for r in rows if r[3][1] is not None)
    out.write("least q for the rung places: %s\n" % dict(sorted(lq.items())))
    out.write("placed with q <= 8 or no rung: %d; q 9..16: %d; q 17..%d: %d; not placed (q <= %d): %d\n" % (
        sum(1 for r in rows if r[3][0] != 'none' and (r[3][1] is None or r[3][1] <= 8)),
        sum(1 for r in rows if r[3][1] is not None and 9 <= r[3][1] <= 16),
        QMAX, sum(1 for r in rows if r[3][1] is not None and r[3][1] >= 17), QMAX, kinds['none']))
    # least q against the size of the readings (spread d_max/d_min), rung places only
    bins = Counter()
    for r in rows:
        if r[3][1] is not None:
            sp = r[0][-1] / r[0][0]
            b = '<=8' if sp <= 8 else ('<=24' if sp <= 24 else ('<=64' if sp <= 64 else '>64'))
            bins[(b, 'q<=8' if r[3][1] <= 8 else ('q9-16' if r[3][1] <= 16 else 'q>=17'))] += 1
    out.write("rung places by spread and q: %s\n" % dict(sorted(bins.items())))
    miss = [r for r in rows if r[3][0] == 'none']
    if miss:
        out.write("not placed, listed (first 20): %s\n" % [(r[0], str(8 * r[0][0] * r[1]), r[2]) for r in miss[:20]])
        pert = pool.map(perturb, [r[0] for r in miss[:200]])
        dest = Counter(k for T, res in pert for i, d, k, q in res)
        out.write("not placed, perturbed one reading (first 200): destinations %s\n" % dict(dest.most_common()))
    out.flush()


if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    from coverB_fine_v1 import late_shapes
    out = open('place_general_v1.out', 'w'); out.write(__doc__ + "\n")
    rng = random.Random(11)
    pops = [('readings <= 24, all (control)', list(itertools.combinations(range(1, 25), 7))),
            ('nearest reading 1, readings <= 32, all', [(1,) + c for c in itertools.combinations(range(2, 33), 6)])]
    for top in (48, 96, 200):
        pops.append(('random, readings <= %d (30,000)' % top, [tuple(sorted(rng.sample(range(1, top + 1), 7))) for _ in range(30000)]))
    pops.append(('late band shapes', late_shapes()))
    allrows = {}
    with Pool(8) as pool:
        for name, sets in pops:
            rows = [r for part in pool.map(work, [sets[i::64] for i in range(64)]) for r in part]
            allrows[name] = rows
            report(name, rows, out, pool)
        samp = [r[0] for r in allrows['readings <= 24, all (control)']][::400] + [r[0] for r in allrows['late band shapes']][::30]
        a = pool.map(classify, samp); b = pool.map(classify, [tuple(3 * d for d in T) for T in samp])
    diff = sum(1 for x, y in zip(a, b) if x[3] != y[3])
    out.write("\nscale check (S vs 3S): %d of %d classified differently\n" % (diff, len(samp)))
    out.close()
    print(open('place_general_v1.out').read()[len(__doc__):])
