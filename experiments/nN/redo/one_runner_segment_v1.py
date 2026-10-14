"""E384 (2026-10-05), one_runner_segment_v1: the closedness of the lonely set along ONE moving reading, six readings frozen.

Owner: "ok do this" (the one-runner segment of PathWindowN, six readings frozen as in M037).
CLASS: frozen readings = six distinct whole numbers (any scale), moving reading d > 0.  The frozen six's clear set C6 is
periodic with period 1 and non-empty (order seven, margin 1/7).  The lonely set along d is {d : some t in C6 has
||d t|| >= 1/8}.
DERIVED BEFORE THE RUN (by hand; the check is exact):
 D1. For rational d = p/q in lowest terms with q >= 2 the reading d, over the instants u + j (u in C6 ∩ (0,1], j = 0..q-1),
     takes the q positions d u + k/q (k = 0..q-1), spaced 1/q <= 1/2 round the circle; the clear band [1/8, 7/8] is the
     closed arc of length 3/4, the blocked arc (-1/8, 1/8) is open of length 1/4; q >= 2 equally spaced points cannot all
     lie in an open arc of length 1/4.  So some instant u + j with j < q has every reading clear: the least lonely
     instant (the cascade's landing) is < q.   PREDICTION P1: landing(d) < q for every non-integer rational d.
 D2. Hence the only values of d at which loneliness of the (six + d) arrangement is not forced by D1 are integers
     (q = 1: the position d u + j p is fixed mod 1 as j runs), where it is the whole-number arrangement itself.
CHECKS (exact Fractions): P1 on every sampled (six, d = p/q); and at integer d* the landing of d* and of d* ± 10^-k, to see
whether the landing of nearby non-integer d runs off as d -> d* (the escape) or stays near the landing of d*.
Misses of P1 are listed individually.
"""
import sys, random, math
from fractions import Fraction as F
from multiprocessing import Pool
import deform_pinch_v1 as D


def landing(ds):
    return D.cascade_landing(ds, cap=200000)


def study(args):
    seed, = args
    rng = random.Random(seed)
    six = sorted(rng.sample(range(1, 41), 6))
    base = [F(x) for x in six]
    p1 = []
    for _ in range(40):
        q = rng.randint(2, 12)
        p = rng.randint(1, 45 * q)
        if math.gcd(p, q) != 1:
            continue
        d = F(p, q)
        if d in base:
            continue
        ds = sorted(base + [d])
        t = landing(ds)
        p1.append((d, q, t, t is not None and t < q))
    ints = []
    for dstar in rng.sample([x for x in range(1, 61) if x not in six], 6):
        row = [dstar, landing(sorted(base + [F(dstar)]))]
        for k in (3, 5, 7, 9):
            e = F(1, 10 ** k)
            row.append((k, landing(sorted(base + [F(dstar) + e])), landing(sorted(base + [F(dstar) - e]))))
        ints.append(row)
    return six, p1, ints


if __name__ == '__main__':
    out = open('one_runner_segment_v1.out', 'w'); out.write(__doc__ + "\n")
    with Pool(4) as pool:
        res = pool.map(study, [(s,) for s in range(300)])
    n = sum(len(p) for _, p, _ in res); hit = sum(1 for _, p, _ in res for r in p if r[3])
    out.write("P1 over %d (six, d) pairs: landing < q in %d; misses %d\n" % (n, hit, n - hit))
    for six, p, _ in res:
        for d, q, t, ok in p:
            if not ok:
                out.write("  MISS six=%s d=%s q=%d landing=%s\n" % (six, d, q, t))
    # integers
    big = 0; tot = 0; none = 0
    worst = []
    for six, _, ints in res:
        for row in ints:
            dstar, t0 = row[0], row[1]
            tot += 1
            if t0 is None:
                none += 1; out.write("  NO LANDING at integer d*=%d, six=%s\n" % (dstar, six)); continue
            for k, tp, tm in row[2:]:
                for tt in (tp, tm):
                    if tt is None:
                        out.write("  NO LANDING near d*=%d (1e-%d), six=%s\n" % (dstar, k, six)); continue
                    worst.append((float(tt / t0), dstar, six, k))
    worst.sort(reverse=True)
    out.write("integer d*: %d cases, landing none %d.  largest ratio landing(d* ± eps)/landing(d*) over eps = 1e-3,1e-5,1e-7,1e-9:\n" % (tot, none))
    for w in worst[:15]:
        out.write("  ratio %.6g  d*=%d six=%s eps=1e-%d\n" % w)
    out.write("count with ratio > 1.001: %d of %d\n" % (sum(1 for w in worst if w[0] > 1.001), len(worst)))
    out.close()
    print(open('one_runner_segment_v1.out').read()[len(__doc__):])
