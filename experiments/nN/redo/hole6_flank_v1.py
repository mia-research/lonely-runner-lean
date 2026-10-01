"""E249/E250 (2026-10-01): phase 3b.  The f = 6 landings in flank terms, and the nested actual stretches, inside c's first
arc [1/(8c), 7/(8c)].  Design: log E249.  Population: the E235 and E243 f = 6 configurations not settled by K0 (E248).
"""
import sys, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8
import holef_cascade_v1 as HF, hole6_wide_v1 as W


def lonely(S, t):
    return all(cd(d * t) >= E8 for d in S)


def study(cb):
    core, block = cb
    c = core[0]; S = tuple(sorted(core + block))
    lo, hi = F(1, 8 * c), F(7, 8 * c)
    if lonely(S, lo):
        return None
    chk = Counter()
    flanks = []
    for h in block:
        K0 = math.ceil((8 * h * lo - 1) / 8); K1 = math.floor((8 * h * hi - 1) / 8)
        first = None; nclear = 0
        for K in range(K0, K1 + 1):
            ok = all(1 <= (x * (8 * K + 1) / F(h)) % 8 <= 7 for x in block)
            if ok:
                nclear += 1
                if first is None:
                    first = K - K0
                    t = F(8 * K + 1, 8 * h)
                    if not lonely(S, t):
                        chk['clear opening not lonely'] += 1
        flanks.append(dict(h=h, L=K1 - K0 + 1, first=first, nclear=nclear,
                           t=F(8 * (K0 + first) + 1, 8 * h) if first is not None else None))
    win = min((f for f in flanks if f['t'] is not None), key=lambda f: f['t'])
    ts, _ = trace(S)
    if win['t'] != ts:
        chk['winner is not the cascade landing'] += 1
    h = win['h']
    walkers = [(x, F(x, h) - math.floor(F(x, h))) for x in block if x != h]
    ghat = sorted(round(float(min(fj, 1 - fj)), 3) for x, fj in walkers)
    lam = []
    for k in range(0, 6):
        cs = clear_set([c] + list(block[:k]), 8 * lo, 8 * hi)
        L = max(b - a for a, b in cs) / 8 if cs else F(0)
        lam.append(float(4 * block[k] * L))
    return dict(core=core, block=block, chk=chk, nflank_clear=sum(1 for f in flanks if f['first'] is not None),
                shadowed=[block.index(f['h']) + 1 for f in flanks if f['first'] is None],
                rank=block.index(h) + 1, j=win['first'], L=win['L'], ghat=ghat, lam=lam,
                ratios=[round(b / a, 3) for a, b in zip(block, block[1:])])


if __name__ == '__main__':
    pops = [('E235 f=6 (ratios below 2)', HF.gen(6, 240, 1000)[0]), ('E243 f=6 (some ratio 2 to 9)', W.gen(242, 1000)[0])]
    out = open('hole6_flank_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    for name, pop in pops:
        with Pool(8) as pool:
            res = [r for r in pool.map(study, pop, chunksize=10) if r]
        ck = Counter()
        for r in res:
            ck.update(r['chk'])
        w("\n== %s: %d configurations not settled by K0 ==" % (name, len(res)))
        w("  CHECKS: %s" % (dict(ck) if ck else '0 failures'))
        w("  flanks with a clear opening inside c's first arc (of 6): %s" % dict(sorted(Counter(r['nflank_clear'] for r in res).items())))
        w("  shadowed flanks by rank (1 = slowest): %s" % dict(sorted(Counter(k for r in res for k in r['shadowed']).items())))
        w("  winner (rank, index j from the arc's first opening of that flank): %s" % dict(sorted(Counter((r['rank'], r['j']) for r in res).items())))
        w("  winner's openings inside the arc, L (floor of log2): %s" % dict(sorted(Counter(int(math.log2(r['L'])) for r in res).items())))
        w("  at the winner, the largest walker step max ghat (tenths): %s" % dict(sorted(Counter(int(10 * r['ghat'][-1]) / 10 for r in res).items())))
        for k in range(6):
            vals = [r['lam'][k] for r in res]
            w("  level %d (c and the %d slowest block readings): 4 x_%d lambda_%d  least %.4f; below 1 in %d" % (k, k, k + 1, k, min(vals), sum(1 for v in vals if v < 1)))
        bad = [r for r in res if min(r['lam']) < 1]
        w("  configurations with some level below 1 (%d), first 15: %s" % (len(bad), [(r['block'], [round(v, 3) for v in r['lam']]) for r in bad[:15]]))
    out.close()
    print(open('hole6_flank_v1.out').read()[len(__doc__):])
