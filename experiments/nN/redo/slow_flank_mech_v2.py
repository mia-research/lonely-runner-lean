"""E266 (2026-10-02): slow_flank_mech_v1 corrected and extended.  Design: log E265; corrections in E266.
(a) the cascade's landing flank is read from trace() by the record's convention (the runner x with 8 x t = 1 mod 8; c's own flank included),
    not as the earliest first-clear CLUSTER opening; (b) perturbation validity = distinct, c least, c never in the way inside any run
    (E260's check), instead of the cluster >= 25c filter that skipped mode B; (c) per-rank state counts, members and random clusters,
    and the joint state of ranks 1 and 2 in random clusters."""
import sys, os, json, random
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE); sys.path.insert(0, '../band_cert_v1'); sys.path.insert(0, HERE)
from slow_flank_mech_v1 import state, run_us, lonely, rand_cluster, flank_info
from hole_C1_flanks_v1 import inway
from e151_block_v1 import trace


def valid(c, cl):
    if len(set(cl)) < 6 or min(cl) <= c: return False
    return not any(inway(c, u, e) for e in cl for u in run_us(c, e))


def land_flank(c, cl):
    S = tuple([c] + sorted(cl)); ts, _ = trace(S)
    assert lonely(S, ts)
    hs = [x for x in S if (8 * x * ts) % 8 == 1]
    h = hs[0]
    return ('c' if h == c else sorted(cl).index(h) + 1), ts


def members_job(item):
    seed, mode, S = item; c = S[0]; cl = list(S[1:])
    return [state(c, cl, e)['state'] for e in cl], land_flank(c, cl)[0]


def rand_job(seed):
    rnd = random.Random(seed); rows = []
    for _ in range(300):
        c, cl = rand_cluster(rnd)
        if not valid(c, cl): continue
        rows.append(([state(c, cl, e)['state'] for e in cl], land_flank(c, cl)[0]))
    return rows


def shifts(item):
    seed, mode, S = item; c = S[0]; cl = list(S[1:]); e1 = cl[0]
    base = land_flank(c, cl)[0]; per = {}
    for j in range(6):
        for d in (-0.25, -0.1, -0.05, -0.01, 0.01, 0.05, 0.1, 0.25):
            cl2 = list(cl); cl2[j] = cl[j] + int(round(d * e1)); cl2 = sorted(cl2)
            if not valid(c, cl2): continue
            st1 = state(c, cl2, cl2[0])['state']; lf = land_flank(c, cl2)[0]
            per.setdefault(j + 1, []).append((d, st1, lf))
    return seed, mode, S, base, per


if __name__ == '__main__':
    items = [tuple(i[:2]) + (tuple(i[2]),) for i in json.load(open('members_5978_v1.json'))]
    out = open('slow_flank_mech_v2.out', 'w'); out.write(__doc__ + "\n")
    def w(s): out.write(s + "\n"); out.flush()
    with Pool(10) as pool:
        res = pool.map(members_job, items, chunksize=40)
        w("[A] members (%d): state by cluster rank" % len(res))
        for rk in range(6): w("   rank %d: %s" % (rk + 1, dict(Counter(st[rk] for st, _ in res))))
        w("   landing flank by the record's convention: %s" % dict(sorted(Counter(str(l) for _, l in res).items())))
        w("   landing flank among members whose rank 1 is not free (21): %s" % dict(sorted(Counter(str(l) for st, l in res if st[0] != 'free').items())))
        rr = [r for part in pool.map(rand_job, range(40)) for r in part]
        w("\n[B] random clusters with c never in the way (%d): state by rank" % len(rr))
        for rk in range(6): w("   rank %d: %s" % (rk + 1, dict(Counter(st[rk] for st, _ in rr))))
        w("   rank 1 and rank 2 both shadowed: %d; no free cluster flank: %d; landing flank: %s" % (
            sum(1 for st, _ in rr if st[0] != 'free' and st[1] != 'free'), sum(1 for st, _ in rr if 'free' not in st), dict(sorted(Counter(str(l) for _, l in rr).items()))))
        exc = [it for it, r in zip(items, res) if r[0][0] != 'free']
        P = pool.map(shifts, exc)
    w("\n[C] the %d rank-1 exceptions perturbed (each walker shifted by d*e1, d in +-0.01, 0.05, 0.1, 0.25; valid shifts only; CHECK: trace's t is lonely, asserted)" % len(P))
    for seed, mode, S, base, per in P:
        c = S[0]
        line = []
        for j in sorted(per):
            r = per[j]; fr = sum(1 for d, s1, lf in r if s1 == 'free')
            line.append("w%d: %d/%d free%s" % (j, fr, len(r), ' land %s' % dict(Counter(str(lf) for d, s1, lf in r if s1 != 'free')) if fr < len(r) else ''))
        w("seed %d %s base landing %s: %s" % (seed, mode, base, '; '.join(line)))
    out.close(); print(open('slow_flank_mech_v2.out').read()[len(__doc__):])
