"""E233 (2026-10-01): the cascade inside the hole ArrBlockRule8 3 9, part 3: every path that differs, read move by move.

Same 2,000 configurations as hole3_cascade_v1/v2.  The paths read in full: the 28 landing in the core's second lonely
stretch, the 5 that do not pass through tau_C, and every core whose first stretch is a single point.  For each move:
the instant in laps of x1 from tau_C, where it lies (inside core stretch k, or in the gap after stretch k), the setter
(C core / B block, with the reading), the readings in the way split C/B.
Checks (forced by A.1, the move depends only on the instant and the readings in the way):
  F1  a move made from an instant inside a core stretch has only block setters (the core is clear there);
  F2  t* is the block's own relay (the three block readings alone) run from the path's first instant inside the stretch
      that holds t*.
"""
import sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8
from hole3_cascade_v2 import run_from
import hole3_cascade_v1 as H


def region(R, cells):
    for k, (a, b) in enumerate(cells):
        if a <= R <= b:
            return 'S%d' % k
        if R < a:
            return 'gap%d' % (k - 1) if k else 'pre'
    return 'beyond'


def study(args):
    core, block = args
    S = tuple(sorted(core + block)); c1 = core[0]; x1 = block[0]
    tc, _ = trace(core); ts, moves = trace(S)
    cells = clear_set([F(d, c1) for d in core], 8 * c1 * tc, 8 * c1 * ts + 400)
    R = lambda t: 8 * c1 * t
    lap = lambda t: float((t - tc) * x1)
    chk = Counter(); rows = []
    for t, way, st, nx in moves:
        reg = region(R(t), cells)
        cls = 'C' if min(st) in core else 'B'
        if reg.startswith('S') and cls == 'C':
            chk['F1'] += 1
        rows.append((lap(t), reg, cls, min(st), tuple(d for d in way if d in core), tuple(d for d in way if d in block), lap(nx), region(R(nx), cells)))
    insts = [mv[0] for mv in moves] + [ts]
    k_land = region(R(ts), cells)
    entry = next(t for t in insts if region(R(t), cells) == k_land)
    if run_from(block, entry) != ts:
        chk['F2'] += 1
    a0, b0 = cells[0]
    return dict(core=core, block=block, chk=chk, rows=rows, k_land=k_land, passes=tc in insts,
                point=(a0 == b0), LC=float((b0 - a0) / (8 * c1) * x1),
                cells=[(round(float((a - R(tc)) / (8 * c1) * x1), 4), round(float((b - R(tc)) / (8 * c1) * x1), 4)) for a, b in cells[:3]])


if __name__ == '__main__':
    pop = H.gen(232, 2000)
    with Pool(8) as pool:
        res = pool.map(study, pop, chunksize=25)
    out = open('hole3_cascade_v3.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    ck = Counter()
    for r in res:
        ck.update(r['chk'])
    w("CHECKS F1, F2 over all 2,000: %s" % (dict(ck) if ck else '0 failures'))
    w("landing stretch: %s" % dict(Counter(r['k_land'] for r in res)))
    w("move regions over all paths (from-region, setter class): %s" % dict(Counter((x[1], x[2]) for r in res for x in r['rows'])))
    for name, sel in (("landing in the core's second stretch", lambda r: r['k_land'] != 'S0'),
                      ("not passing through tau_C", lambda r: not r['passes']),
                      ("core's first stretch a single point", lambda r: r['point'])):
        grp = [r for r in res if sel(r)]
        w("\n== %s: %d paths ==" % (name, len(grp)))
        for r in grp:
            w("core %s block %s  stretches (laps of x1 from tau_C) %s  lands in %s" % (r['core'], r['block'], r['cells'], r['k_land']))
            for x in r['rows']:
                w("   from %+.4f [%s]  setter %s %d  in the way C%s B%s  -> %+.4f [%s]" % x)
    out.close()
    print(open('hole3_cascade_v3.out').read()[len(__doc__):][:6000])
