"""E253 (2026-10-01): phase 3c, reading the shadowed flanks (hole6_shadow_v1.out): one walker or several?

For each block flank shadowed across c's band run (generic class, every six coprime): the walkers in the way at EVERY
opening of the run (the intersection over the run).  If one exists it shadows the run alone; its ratio x_j/e = A + eps
(A the nearest whole number) and A mod 8, and the derived condition: at u = 8k + 1 (u = 1 mod 8) it reads A + eps*u
(mod 8), so it is in the way at every opening of the run exactly when A + eps*u stays within 1 of a multiple of 8 for all
u in the run (checked exactly; this is the near form of the exact slot-sharer, Theorem 6.8, 8 | A).  If none exists, the
shadow is a hand-off: listed with every walker's (A, eps, A mod 8) and the openings each one covers.
"""
import sys, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
import holef_cascade_v1 as HF, hole6_wide_v1 as W
from hole6_shadow_v1 import study


def read(cb):
    r = study(cb)
    if r is None or r['off']:
        return []
    core, block = r['core'], r['block']; c = core[0]
    out = []
    for f in r['flanks']:
        if f['first'] is not None:
            continue
        e = f['e']
        k0 = math.ceil((F(e, c) - 1) / 8); k1 = math.floor((F(7 * e, c) - 1) / 8)
        us = [8 * k + 1 for k in range(k0, k1 + 1)]
        sets = [set(rank for rank, rd, q, g in op) for op in f['blocked']]
        common = set.intersection(*sets) if sets else set()
        walkers = []
        for x in block:
            if x == e:
                continue
            A = round(F(x, e)); eps = F(x, e) - A
            cover = [i for i, u in enumerate(us) if ((x * u) % (8 * e) < e or (x * u) % (8 * e) > 7 * e)]
            pred = all(min((A + eps * u) % 8, 8 - (A + eps * u) % 8) < 1 for u in us)
            walkers.append(dict(rank=block.index(x) + 1, A=A, A8=A % 8, eps=float(eps), d=int(x - A * e), cover=len(cover), pred_alone=pred,
                                alone=(len(cover) == len(us))))
        out.append(dict(block=block, c=c, e=e, rank=f['rank'], n=len(us), common=sorted(common), walkers=walkers))
    return out


if __name__ == '__main__':
    pops = [('E235 f=6', HF.gen(6, 240, 1000)[0]), ('E243 f=6', W.gen(242, 1000)[0])]
    out = open('hole6_shadow_v2.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    allsh = []
    for name, pop in pops:
        with Pool(8) as pool:
            sh = [x for part in pool.map(read, pop, chunksize=10) for x in part]
        allsh += sh
        alone = [s for s in sh if s['common']]
        w("\n== %s: %d shadowed flanks ==" % (name, len(sh)))
        w("  shadowed by one walker alone (in the way at every opening of the run): %d; by a hand-off: %d" % (len(alone), len(sh) - len(alone)))
        chk = sum(1 for s in sh for wk in s['walkers'] if wk['alone'] != wk['pred_alone'])
        w("  CHECK the derived condition (A + eps*u within 1 of a multiple of 8 for all u in the run) against exact coverage: %d disagreements" % chk)
        w("  the lone walker: (A mod 8, sign of eps): %s" % dict(Counter((wk['A8'], '+' if wk['eps'] > 0 else '-') for s in alone for wk in s['walkers'] if wk['alone'])))
        w("  the lone walker: A: %s; |x_j - A e| / c (tenths): %s" % (dict(Counter(wk['A'] for s in alone for wk in s['walkers'] if wk['alone'])),
            dict(sorted(Counter(int(10 * abs(wk['d']) / s['c']) / 10 for s in alone for wk in s['walkers'] if wk['alone']).items()))))
        for s in sh:
            if not s['common']:
                w("    HAND-OFF  block %s  flank rank %d (e = %d), run %d openings; walkers (rank, A, A mod 8, eps, openings covered): %s" % (
                    s['block'], s['rank'], s['e'], s['n'], [(wk['rank'], wk['A'], wk['A8'], round(wk['eps'], 4), wk['cover']) for wk in s['walkers']]))
    out.close()
    print(open('hole6_shadow_v2.out').read()[len(__doc__):])
