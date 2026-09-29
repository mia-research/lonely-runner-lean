"""E174 (2026-09-29): the place test applied to the boundary incidents.

Owner: "ok now apply the place test to the boundary incidents".  Memory: feedback-n8-cascade-is-the-oracle (place test).

Class: every set of seven distinct whole-number readings in 1..24 (346,104 sets; E100's population).
The incident: the cascade lands at t* (first isolation at or after the bound).  Its left boundary is an opening
(8K+1)/(8a) of a host reading a (the bound is the nearest runner's opening on lap 0); its right boundary is the first
closing (8L+7)/(8c) of a closer c.  Tight = the two boundaries coincide (a single-point incident).

Place statements, each checked by exact equality with the cascade's landing t*:
  S0  t* is a named view of E100's menu (cascade_vs_menu_v1.views): the bound B = 1/(8 d_min); a reading's next opening
      O = 9/(8e); rung R1 a/q +- 1/(8 min D_q); nudge N a/8 +- 1/(8 max M_8); reverse R1 V = 9/(8 d_max); ladder L = a/q.
  S1  t* is a named view v (not itself lonely) displaced by one separation: the runner in the subject's slot at v leaves,
      and t* is its exit, t* = nextOpening(c, v) = move(v) (SeparationN.lonely_of_separation; E158: two runners in one
      slot, the isolation waits for them to separate).  The place is (view, captured runner), both given by the readings.
Misses: incidents at neither place.  Each is listed with its boundaries (host, lap, closer, tight).  Misses are then
perturbed through the cascade, one reading moved by +-1 at a time (distinct, positive), and the place where each
perturbed arrangement's isolation lands is recorded (S0 view, S1 view+runner, or a miss again).

Oracle check (CLAUDE.md section 3, not a pass condition on the question): the cascade's landing equals the first lonely
instant computed without the cascade (wave_incident_v1.lonely_components).
"""
import itertools, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from cascade_vs_menu_v1 import views
from quantity_tests_v1 import cd, E8, next_opening
from wave_incident_v1 import lonely_components


def lonely(T, t):
    return t > 0 and all(cd(d * t) >= E8 for d in T)


def move(T, t):
    way = [d for d in T if cd(d * t) < E8]
    if not way:
        return t, None
    nx = max(next_opening(d, t) for d in way)
    return nx, [d for d in way if next_opening(d, t) == nx]


def cascade(T):
    t = F(1, 8 * T[0]); n = 0
    while True:
        nx, setters = move(T, t)
        if setters is None:
            return t, n
        t = nx; n += 1


def boundaries(T, t):
    rank = {d: i for i, d in enumerate(T)}
    openers = [d for d in T if d * t - math.floor(d * t) == E8]
    ends = {d: (math.floor(d * t) + F(7, 8)) / d for d in T}
    w = min(ends.values())
    closers = [d for d in T if ends[d] == w]
    a = max(openers) if openers else None
    return dict(host=rank[a] if a else None, K=math.floor(a * t) if a else None,
                closer=rank[min(closers)], L=math.floor(min(closers) * t), tight=(w == t))


def place(T, ts):
    V = views(T)
    for k, t in V.items():
        if t == ts:
            return ('S0', k[0], k)
    for k, v in sorted(V.items(), key=lambda kv: kv[1]):
        if v >= ts or lonely(T, v):
            continue
        nx, setters = move(T, v)
        if nx == ts:
            return ('S1', k[0], k, tuple(sorted(setters)))
    return ('miss',)


def classify(T):
    ts, n = cascade(T)
    return ts, n, place(T, ts)


def chunk(first):
    out = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        ts, n, p = classify(T)
        comps = lonely_components(T, F(1, 8 * T[0]), ts + F(2, T[0]))
        c1 = bool(comps) and comps[0][0] == ts
        out.append((T, ts, n, p, c1))
    return out


def perturb(T):
    res = []
    for i in range(7):
        for dlt in (-1, 1):
            U = list(T); U[i] += dlt
            if U[i] < 1 or len(set(U)) < 7:
                continue
            U = tuple(sorted(U))
            ts, n, p = classify(U)
            res.append((i, dlt, U, float(8 * U[0] * ts), p[0], p[1] if len(p) > 1 else None))
    return T, res


if __name__ == '__main__':
    out = open('place_incidents_v1.out', 'w'); out.write(__doc__ + "\n")
    with Pool(8) as pool:
        rows = [r for part in pool.map(chunk, range(1, 19)) for r in part]
    out.write("sets: %d\noracle check (landing = independent first lonely instant): %d violations\n" %
              (len(rows), sum(not r[4] for r in rows)))
    kinds = Counter(r[3][0] for r in rows)
    out.write("S0 (a named view): %d   S1 (a view displaced by one separation): %d   misses: %d\n" %
              (kinds['S0'], kinds['S1'], kinds['miss']))
    out.write("S0 by view family: %s\n" % dict(Counter(r[3][1] for r in rows if r[3][0] == 'S0').most_common()))
    s1 = [r for r in rows if r[3][0] == 'S1']
    out.write("S1 by view family: %s\n" % dict(Counter(r[3][1] for r in s1).most_common()))
    out.write("S1 captured runner, by view family and rank: %s\n" %
              dict(Counter((r[3][1], tuple(r[0].index(c) for c in r[3][3])) for r in s1).most_common(20)))
    # at the bound, the captured runner: |c - 8 n m| < m (within 1/8 of a lap at 1/(8m))
    b1 = [r for r in s1 if r[3][1] == 'B']
    out.write("S1 at the bound: %d; captured runner within m of a multiple of 8m in %d\n" %
              (len(b1), sum(all(abs(c - 8 * round(c / (8 * r[0][0])) * r[0][0]) < r[0][0] for c in r[3][3]) for r in b1)))
    misses = [r for r in rows if r[3][0] == 'miss']
    out.write("\nmisses: %d; chain length from the bound: %s\n" % (len(misses), dict(sorted(Counter(r[2] for r in misses).items()))))
    bd = [boundaries(r[0], r[1]) for r in misses]
    out.write("misses, incident boundaries: tight %d; host rank %s; closer rank %s\n" %
              (sum(b['tight'] for b in bd), dict(sorted(Counter(b['host'] for b in bd).items(), key=str)),
               dict(sorted(Counter(b['closer'] for b in bd).items()))))
    out.write("misses, listed (first 40): readings, R = 8 d_min t*, moves, host rank/lap, closer rank/lap, tight\n")
    for (T, ts, n, p, c1), b in list(zip(misses, bd))[:40]:
        out.write("   %s  R=%s  moves=%d  host %s/K%s  closer %s/L%s  tight=%s\n" %
                  (T, 8 * T[0] * ts, n, b['host'], b['K'], b['closer'], b['L'], b['tight']))
    out.flush()
    # perturb every miss through the cascade, one reading at a time
    with Pool(8) as pool:
        pert = pool.map(perturb, [r[0] for r in misses])
    where = Counter(); back = Counter()
    for T, res in pert:
        for i, dlt, U, R, kind, fam in res:
            where[(kind, fam)] += 1
        back[sum(1 for x in res if x[4] != 'miss')] += 1
    out.write("\nperturbation of the misses (one reading +-1): where the isolation lands %s\n" % dict(where.most_common()))
    out.write("misses by how many of their +-1 perturbations land at S0 or S1: %s\n" % dict(sorted(back.items())))
    out.write("\nfirst 12 misses, perturbations traced (rank moved, delta, new readings, R, place):\n")
    for T, res in pert[:12]:
        out.write("   %s\n" % (T,))
        for i, dlt, U, R, kind, fam in res:
            out.write("      rank %d %+d -> %s  R=%.4f  %s %s\n" % (i, dlt, U, R, kind, fam or ''))
    out.close()
    print(open('place_incidents_v1.out').read()[len(__doc__):])
