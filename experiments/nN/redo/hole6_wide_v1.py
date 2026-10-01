"""E242/E243 (2026-10-01): the f = 6 hole beyond consecutive ratio 2.  Design: log E242.

Core: the one reading c = 1000.  Block: x1/c uniform in [9, 60]; consecutive ratios log-uniform in [1, 9); kept if some
consecutive ratio is >= 2, x6/x1 <= 64 (search range), and no proved rule covers the set (holef_cascade_v1.covered).
Checks: C1, t* >= tau_C, t* in a core stretch, F1, F2 (holef_cascade_v1.study); G1-G3 (hole_g_flank_v1.study);
I1-I3 (hole_isolations_v1.study, all 500 arcs of c in (0, 1/2]).
"""
import sys, math, random, json, gzip
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
import holef_cascade_v1 as HF, hole_g_flank_v1 as G, hole_isolations_v1 as I


def gen(seed, n):
    rng = random.Random(seed); out = []; excl = Counter(); c = 1000
    while len(out) < n:
        x = [int(round(c * rng.uniform(9, 60)))]
        for _ in range(5):
            x.append(int(round(x[-1] * math.exp(rng.uniform(0, math.log(9))))))
        if len(set(x)) < 6 or x[-1] > 64 * x[0]:
            excl['outside the search range'] += 1; continue
        if max(b / a for a, b in zip(x, x[1:])) < 2:
            excl['every ratio below 2 (E235 population)'] += 1; continue
        rule = HF.covered([c] + x)
        if rule:
            excl[rule] += 1; continue
        out.append(((c,), tuple(x)))
    return out, excl


def study(cb):
    core, block = cb
    a = HF.study((core, block))
    g = G.study((6, core, block, 'tau_C'))
    i, ick = I.study((6, core, block))
    return a, g, i, ick


if __name__ == '__main__':
    pop, excl = gen(242, 1000)
    with Pool(8) as pool:
        res = pool.map(study, pop, chunksize=5)
    out = open('hole6_wide_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    with gzip.open('hole6_wide_isolations_v1.jsonl.gz', 'wt') as z:
        for a, g, i, ick in res:
            z.write(json.dumps(i) + "\n")
    w("excluded while sampling: %s" % dict(excl))
    w("kept: %d; max consecutive ratio of the kept (floor): %s" % (len(pop), dict(sorted(Counter(int(max(b / a for a, b in zip(bl, bl[1:]))) for c, bl in pop).items()))))
    w("spread x6/x1 of the kept (floor of log2): %s" % dict(sorted(Counter(int(math.log2(bl[-1] / bl[0])) for c, bl in pop).items())))
    ck = Counter()
    for a, g, i, ick in res:
        ck.update(a['chk']); ck.update(g['chk']); ck.update(ick)
    w("CHECKS (C1, t* >= tau_C, t* in a core stretch, F1, F2, G1, G2, G3, I1, I2, I3): %s" % (dict(ck) if ck else '0 failures'))
    w("landing stretch (c's arc): %s" % dict(Counter(a['k_land'] for a, g, i, ick in res)))
    w("block clear at tau_C: %d" % sum(g['clear0'] for a, g, i, ick in res))
    nz = [g for a, g, i, ick in res if not g['clear0']]
    w("winner (rank, j): %s" % dict(sorted(Counter((g['rank'], g['j']) for g in nz).items())))
    w("moves of the block's relay from tau_C: %s" % dict(sorted(Counter(g['moves'] for g in nz).items())))
    w("block relay from tau_C, laps of x1 (record): max %.4f" % max(a['gB'] for a, g, i, ick in res))
    nohold = Counter(sum(1 for s in i['st'] if not s[4]) for a, g, i, ick in res)
    w("configurations by the number of c's arcs in (0, 1/2] holding no isolation: %s" % dict(sorted(nohold.items())))
    longest = Counter()
    for a, g, i, ick in res:
        best = cur = 0
        for s in i['st']:
            cur = cur + 1 if not s[4] else 0; best = max(best, cur)
        longest[best] += 1
    w("longest run of arcs holding none: %s" % dict(sorted(longest.items())))
    odd = [(a, g) for a, g, i, ick in res if a['k_land'] != 'S0']
    w("configurations landing beyond c's first arc: %d" % len(odd))
    for a, g in odd[:20]:
        HF.dump(w, a)
    empty = [(a, i) for a, g, i, ick in res if any(not s[4] for s in i['st'])]
    w("configurations with some arc holding none (%d), first 10: %s" % (len(empty), [(a['block'], [k for k, s in enumerate(i['st']) if not s[4]][:8]) for a, i in empty[:10]]))
    out.close()
    print(open('hole6_wide_v1.out').read()[len(__doc__):])
