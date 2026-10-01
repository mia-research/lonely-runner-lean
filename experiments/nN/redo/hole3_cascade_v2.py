"""E233 (2026-10-01): the cascade inside the hole ArrBlockRule8 3 9, part 2: the block's relay time from tau_C against the
core's first lonely stretch, both in laps of the block's slowest reading x1.

Same 2,000 configurations as hole3_cascade_v1.  Per configuration (exact):
  L_C = length of the core's first lonely stretch (the clear interval of the four core readings starting at tau_C);
  g_B = time from tau_C to the block's own first lonely instant at or after tau_C (the three block readings alone,
        the cascade run from tau_C);
both times x1 (laps of x1).  Forced (a check): t* is in the core's first stretch iff g_B <= L_C; then t* = tau_C + g_B.
Records: L_C and g_B for every path; the 28 that land in the core's second stretch read in full (L_C, g_B, and the
second stretch).
"""
import sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8, next_opening
import hole3_cascade_v1 as H


def run_from(S, t):
    while True:
        way = [d for d in S if cd(d * t) < E8]
        if not way:
            return t
        t = max(next_opening(d, t) for d in way)


def study(args):
    core, block = args
    S = tuple(sorted(core + block)); c1 = core[0]; x1 = block[0]
    tc, _ = trace(core); ts, _ = trace(S)
    cells = clear_set([F(d, c1) for d in core], 8 * c1 * tc, 8 * c1 * tc + 400)
    a0, b0 = cells[0]
    LC = (b0 - a0) / (8 * c1) * x1
    tb = run_from(block, tc)
    gB = (tb - tc) * x1
    in_first = (8 * c1 * ts <= b0)
    chk = (in_first != (gB <= LC)) or (in_first and ts != tb)
    second = None
    if not in_first and len(cells) > 1:
        a1, b1 = cells[1]
        second = (float((a1 - a0) / (8 * c1) * x1), float((b1 - a1) / (8 * c1) * x1))
    return dict(core=core, block=block, LC=LC, gB=gB, in_first=in_first, chk=chk, second=second,
                spreadB=float(F(block[2], block[0])), spreadC=float(F(core[3], core[0])))


def bins(vals, edges):
    c = Counter()
    for v in vals:
        for e in edges:
            if v <= e:
                c['<= %s' % e] += 1; break
        else:
            c['> %s' % edges[-1]] += 1
    return dict(c)


if __name__ == '__main__':
    pop = H.gen(232, 2000)
    with Pool(8) as pool:
        rows = pool.map(study, pop, chunksize=25)
    out = open('hole3_cascade_v2.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    w("CHECK (t* in the first stretch iff g_B <= L_C; then t* = the block's own landing): %d failures" % sum(r['chk'] for r in rows))
    w("L_C, the core's first stretch, in laps of x1: %s" % bins([float(r['LC']) for r in rows], [0, 0.25, 0.5, 1, 2, 4, 8, 16]))
    w("g_B, the block's relay time from tau_C, in laps of x1: %s" % bins([float(r['gB']) for r in rows], [0, 0.25, 0.5, 0.75, 1, 1.5, 2]))
    w("largest g_B over all paths: %.4f laps of x1" % max(float(r['gB']) for r in rows))
    w("smallest L_C among paths landing in the first stretch: %.4f; largest L_C among those landing later: %.4f" %
      (min(float(r['LC']) for r in rows if r['in_first']), max(float(r['LC']) for r in rows if not r['in_first'])))
    w("the 28 landing later, read in full (core, block, L_C, g_B, second stretch start and length, in laps of x1):")
    for r in rows:
        if not r['in_first']:
            w("  core %s block %s  L_C %.4f  g_B %.4f  second stretch at %s  core spread %.3f" %
              (r['core'], r['block'], float(r['LC']), float(r['gB']), tuple(round(x, 4) for x in r['second']) if r['second'] else None, r['spreadC']))
    out.close()
    print(open('hole3_cascade_v2.out').read()[len(__doc__):])
