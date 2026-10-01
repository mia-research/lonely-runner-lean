"""E247/E248 (2026-10-01): step 3 phase 3a.  Which mechanism already in the record names an isolation inside c's first arc,
for each f = 6 configuration of E235 (1,000) and E243 (1,000)?  Design: log E247.

K0  block clear at c's exit 1/(8c).
K1  sync_block (SyncBlockN): carrier N = x1, offsets e = x_i - x1, Emax = x6 - x1; at a named start t0 (c's exit, or k/q with
    q <= 12) with [t0, t0 + 1/N] inside c's first arc; y = middle of the widest gap of {e t0 mod 1}; hypothesis: every
    offset at distance >= 1/8 + Emax/N from y.  Named instant t0 + fract(-y - N t0)/N.
K2  as K1 with carrier the block reading minimising max|x_i - N|/N, signed offsets ([derived] extension of sync_block).
Checks: every named instant lies in c's first arc and the full set is lonely there (exact); every hypothesis that holds
gives a lonely instant (sync_block is proved, so a failure would be a fault in this script).
"""
import sys, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
from quantity_tests_v1 import cd, E8
import holef_cascade_v1 as HF, hole6_wide_v1 as W

QMAX = 12


def lonely(S, t):
    return all(cd(d * t) >= E8 for d in S)


def widest_gap_mid(pts):
    p = sorted(x - math.floor(x) for x in pts)
    best = None
    for a, b in zip(p, p[1:] + [p[0] + 1]):
        if best is None or b - a > best[0]:
            best = (b - a, (a + b) / 2)
    return best


def sync_try(block, N, t0):
    offs = [x - N for x in block]
    Emax = max(abs(e) for e in offs)
    gap, y = widest_gap_mid([e * t0 for e in offs])
    margin = F(1, 8) + F(Emax) / N
    dmin = min(cd(y - e * t0) for e in offs)
    if dmin < margin:
        return None
    t = t0 + ((-y - N * t0) - math.floor(-y - N * t0)) / N
    return t


def study(cb):
    core, block = cb
    c = core[0]; S = tuple(sorted(core + block))
    lo, hi = F(1, 8 * c), F(7, 8 * c)
    starts = [lo] + sorted({F(k, q) for q in range(1, QMAX + 1) for k in range(1, q) if lo <= F(k, q) and F(k, q) + F(1, block[0]) <= hi})
    res = {'K0': lonely(S, lo)}
    chk = Counter()
    Nbest = min(block, key=lambda N: max(abs(x - N) for x in block) / N)
    for name, N in (('K1', block[0]), ('K2', Nbest)):
        res[name] = None
        for t0 in starts:
            if t0 + F(1, N) > hi:
                continue
            t = sync_try(block, N, t0)
            if t is not None:
                if not (lo <= t <= hi and lonely(S, t)):
                    chk['sync hypothesis held but not lonely in the arc'] += 1
                res[name] = t0; break
    spread = block[-1] / block[0]
    ratios = [round(b / a, 3) for a, b in zip(block, block[1:])]
    return dict(core=core, block=block, res=res, chk=chk, spread=spread, ratios=ratios,
                emax_n=float(max(abs(x - Nbest) for x in block) / Nbest))


if __name__ == '__main__':
    pops = [('E235 f=6 (ratios below 2)', HF.gen(6, 240, 1000)[0]), ('E243 f=6 (some ratio 2 to 9)', W.gen(242, 1000)[0])]
    out = open('hole6_mech_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    for name, pop in pops:
        with Pool(8) as pool:
            res = pool.map(study, pop, chunksize=10)
        ck = Counter()
        for r in res:
            ck.update(r['chk'])
        w("\n== %s: %d configurations ==" % (name, len(res)))
        w("  CHECKS: %s" % (dict(ck) if ck else '0 failures'))
        reach = Counter()
        for r in res:
            key = 'K0' if r['res']['K0'] else ('K1' if r['res']['K1'] is not None else ('K2' if r['res']['K2'] is not None else 'none'))
            reach[key] += 1
        w("  first mechanism that names an isolation in c's first arc: %s" % dict(reach))
        w("  configurations reached by K1 or K2, by max|x_i - N|/N of the best carrier (tenths): %s" % dict(sorted(Counter(
            int(10 * r['emax_n']) / 10 for r in res if not r['res']['K0'] and (r['res']['K1'] is not None or r['res']['K2'] is not None)).items())))
        un = [r for r in res if not r['res']['K0'] and r['res']['K1'] is None and r['res']['K2'] is None]
        w("  not reached (%d): by spread x6/x1 (floor of log2): %s" % (len(un), dict(sorted(Counter(int(math.log2(r['spread'])) for r in un).items()))))
        w("  not reached, by the best carrier's max|x_i - N|/N (tenths): %s" % dict(sorted(Counter(int(10 * r['emax_n']) / 10 for r in un).items())))
        w("  not reached, first 15: %s" % [(r['block'], r['ratios']) for r in un[:15]])
    out.close()
    print(open('hole6_mech_v1.out').read()[len(__doc__):])
