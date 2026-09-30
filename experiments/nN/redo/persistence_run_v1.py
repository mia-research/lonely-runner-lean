"""E218/E219 (2026-10-01): the persistence-region run.  Design: log E218.

The cascade's landing is a certificate: the setter h on its leaving edge at lap K, t = (8K+1)/(8h), and every other
reading d in the clear block [8k_d+1, 8k_d+7] holding p_d = (8K+1)*d/h.  With h fixed its persistence region is a box
(M4-1): each d separately in [(8k_d+1)h/(8K+1), (8k_d+7)h/(8K+1)].  Faces: d at its leaving edge or its entering edge.
  A. The landing's box: certificate, slacks p_d - (8k_d+1) and (8k_d+7) - p_d, tight readings besides the setter;
     box check (sampled arrangements inside the box are lonely at t) and where the cascade lands for them.
  B. Across each face, one reading at a time: the arrangement scaled by L = 1000*(8K+1) so the face is a whole number,
     d moved to one unit past it; the exact cascade's new landing, classified.
Checks: C1 (cascade landing = least clear point from clear_set) at every arrangement run; the box check; the
construction check (the moved reading is in the way at t on the intended side).
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8

Q = 1000


def cert(S):
    S = tuple(sorted(S)); m = S[0]
    ts, moves = trace(S)
    h = min(moves[-1][2]) if moves else m
    K8 = 8 * h * ts - 1
    assert K8.denominator == 1 and K8 % 8 == 0, (S, ts, h)
    K = int(K8) // 8
    laps = {}
    for d in S:
        p = 8 * d * ts
        k = math.floor((p - 1) / 8)
        assert 1 <= p - 8 * k <= 7, (S, d, p)
        laps[d] = (k, p)
    least = clear_set([F(d, m) for d in S], F(1), max(F(40), 8 * m * ts + 1))[0][0]
    return ts, h, K, laps, least == 8 * m * ts, len(moves)


def study_a(args):
    S, seed = args
    S = tuple(sorted(S)); rng = random.Random(seed)
    ts, h, K, laps, c1, nm = cert(S)
    chk = (not c1)
    tight = [d for d in S if d != h and (laps[d][1] - 8 * laps[d][0] in (1, 7))]
    L = Q * (8 * K + 1); t = F(8 * K + 1, 8 * h * L)
    same = Counter()
    for _ in range(10):
        U = {h * L}
        for d in S:
            if d == h:
                continue
            k = laps[d][0]
            U.add(rng.randint((8 * k + 1) * h * Q, (8 * k + 7) * h * Q))
        if len(U) < 7:
            continue
        U = tuple(sorted(U))
        chk += sum(1 for x in U if cd(x * t) < E8)                                   # box check
        ts2, h2, K2, laps2, c12, _ = cert(U)
        chk += (not c12)
        same['same certificate' if (h2 == h * L and K2 == K) else ('earlier instant' if ts2 < t else 'later instant')] += 1
    return dict(S=S, h_rank=S.index(h), K=K, n_tight=len(tight), tight_side=[('leaving' if laps[d][1] - 8 * laps[d][0] == 1 else 'entering') for d in tight],
                same=same, chk=chk, moves=nm)


def study_b(S):
    S = tuple(sorted(S))
    ts, h, K, laps, c1, _ = cert(S)
    chk = (not c1)
    L = Q * (8 * K + 1); t = F(8 * K + 1, 8 * h * L); base = [x * L for x in S]
    rows = []
    for d in S:
        if d == h:
            continue
        k = laps[d][0]
        for face in ('leaving', 'entering'):
            dv = (8 * k + 1) * h * Q - 1 if face == 'leaving' else (8 * k + 7) * h * Q + 1
            U = [x for x in base if x != d * L] + [dv]
            if len(set(U)) < 7 or min(U) <= 0:
                rows.append((face, 'skipped', None)); continue
            U = tuple(sorted(U))
            p = (dv * t * 8) % 8
            chk += not ((face == 'leaving' and p < 1) or (face == 'entering' and p > 7))    # construction
            ts2, h2, K2, laps2, c12, nm2 = cert(U)
            chk += (not c12)
            name = lambda v: 'd' if v == dv else ('the old setter' if v == h * L else 'another reading')
            if face == 'leaving':
                if h2 == dv and 8 * dv * ts2 == 8 * k + 1:
                    cls = 'hand-off to d at its lap'
                elif ts2 < t:
                    cls = 'earlier instant'
                else:
                    cls = 'other: setter %s' % name(h2)
                rows.append((face, cls, None))
            else:
                td = F(8 * k + 9, 8 * dv)
                if h2 == dv and ts2 == td:
                    cls = "d's next opening"
                elif ts2 < t:
                    cls = 'earlier instant'
                else:
                    cls = 'later, setter %s' % name(h2)
                info = None
                if cls != "d's next opening" and ts2 >= t:
                    way = [(name(x), 'entering side' if (8 * x * td) % 8 > 7 else 'leaving side') for x in U if cd(x * td) < E8]
                    info = tuple(sorted(Counter(way).items()))
                rows.append((face, cls, info))
    return dict(S=S, rows=rows, chk=chk)


def fine(seed, n, lo, hi):
    r = random.Random(seed); out = []
    while len(out) < n:
        m = 1000; W = int(r.uniform(lo, hi) * m)
        S = tuple(sorted({m, W} | {r.randrange(m + 1, W) for _ in range(5)}))
        if len(S) == 7:
            out.append(S)
    return out


def report_a(name, rows, w):
    w("\n== A. %s: %d sets ==" % (name, len(rows)))
    w("  CHECKS (C1 at the set and at every sample; box check at every sample): %d failures" % sum(r['chk'] for r in rows))
    w("  readings tight at the landing besides the setter: %s" % dict(sorted(Counter(r['n_tight'] for r in rows).items())))
    w("  their sides: %s" % dict(Counter(s for r in rows for s in r['tight_side'])))
    S = Counter()
    for r in rows:
        S.update(r['same'])
    w("  arrangements sampled inside the landing's box: where the cascade lands: %s" % dict(S))
    w("  setter's rank (0 = slowest): %s" % dict(sorted(Counter(r['h_rank'] for r in rows).items())))


def report_b(name, rows, w):
    w("\n== B. %s: %d sets ==" % (name, len(rows)))
    w("  CHECKS (C1 at every arrangement; construction): %d failures" % sum(r['chk'] for r in rows))
    for face in ('leaving', 'entering'):
        C = Counter(c for r in rows for f, c, i in r['rows'] if f == face)
        w("  %s face: %s" % (face, dict(C.most_common())))
    I = Counter(i for r in rows for f, c, i in r['rows'] if f == 'entering' and i)
    w("  entering crossings not settled at d's next opening: readings in the way there (name, side): %s" % dict(I.most_common(10)))


if __name__ == '__main__':
    out = open('persistence_run_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    p1 = list(itertools.combinations(range(1, 17), 7))
    p3 = fine(219, 1000, 2, 20)
    with Pool(8) as pool:
        report_a('every 7-set of readings <= 16', pool.map(study_a, [(S, i) for i, S in enumerate(p1)], chunksize=50), w)
        report_a('fine shapes, least reading 1,000, spread uniform in [2, 20]', pool.map(study_a, [(S, i) for i, S in enumerate(p3)], chunksize=10), w)
        rng = random.Random(218)
        b1 = rng.sample(p1, 300); b2 = fine(220, 300, 2, 20)
        report_b('300 sets drawn uniformly from the readings <= 16 family', pool.map(study_b, b1), w)
        report_b('300 fine shapes, spread uniform in [2, 20]', pool.map(study_b, b2), w)
    out.close()
    print(open('persistence_run_v1.out').read()[len(__doc__):])
