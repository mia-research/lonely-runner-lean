"""E257/E258 (2026-10-01): the 21 hand-offs of E253, read for persistence and perturbed through the cascade.
Design: log E257.

Part 1: for each hand-off flank, the least number s of consecutive segments of the run's openings, each with one walker in
the way at every opening of it (greedy left to right, exact); per segment the walker's (A, A mod 8, eps) with
x_j / e = A + eps, the segment length in openings and 1/(4|eps|).
Part 2 (E67): every block reading moved by +-1, +-2, one at a time: is the flank still shadowed across c's band run (one
walker, or a hand-off), and where does the cascade land (in c's first arc? which flank)?
Checks: c never in the way inside its run; the earliest first-clear flank opening is the cascade's landing, lonely there.
"""
import sys, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8
import holef_cascade_v1 as HF, hole6_wide_v1 as W
from hole6_shadow_v2 import read as read_shadows


def inway(x, u, e):
    r = (x * u) % (8 * e)
    return r < e or r > 7 * e


def run_us(c, e):
    k0 = math.ceil((F(e, c) - 1) / 8); k1 = math.floor((F(7 * e, c) - 1) / 8)
    return [8 * k + 1 for k in range(k0, k1 + 1)]


def flank_state(c, block, e):
    """('free', index) | ('alone', walker) | ('handoff', s, segments)"""
    us = run_us(c, e)
    sets = []
    for i, u in enumerate(us):
        ins = [x for x in block if x != e and inway(x, u, e)]
        if not ins:
            return ('free', i)
        sets.append(set(ins))
    common = set.intersection(*sets)
    if common:
        return ('alone', min(common))
    segs = []; cur = set(sets[0]); start = 0
    for i in range(1, len(sets)):
        nxt = cur & sets[i]
        if nxt:
            cur = nxt
        else:
            segs.append((start, i - 1, min(cur))); start = i; cur = set(sets[i])
    segs.append((start, len(sets) - 1, min(cur)))
    return ('handoff', len(segs), segs)


def walker_desc(x, e):
    A = round(F(x, e)); eps = F(x, e) - A
    return (A, A % 8, round(float(eps), 4), round(1 / (4 * abs(float(eps))), 1) if eps else None)


def landing(S, c, block):
    ts, _ = trace(S)
    inarc = F(1, 8 * c) <= ts <= F(7, 8 * c)
    h = next((x for x in sorted(S) if ((8 * x * ts) % 8) == 1), None)
    return inarc, (sorted(block).index(h) + 1 if h in block else 'c')


def study(item):
    block, c, e = tuple(item['block']), item['c'], item['e']
    S = tuple(sorted((c,) + block)); chk = Counter()
    us = run_us(c, e)
    for u in us:
        if inway(c, u, e):
            chk['c in the way inside its run'] += 1
    st = flank_state(c, block, e)
    segs = [] if st[0] != 'handoff' else [(a, b, b - a + 1, block.index(x) + 1, walker_desc(x, e)) for a, b, x in st[2]]
    pert = Counter(); freers = []
    for x in block:
        for dlt in (-2, -1, 1, 2):
            nb = tuple(sorted(y + dlt if y == x else y for y in block))
            if len(set(nb)) < 6 or nb[0] <= c:
                continue
            ne = e + dlt if x == e else e
            st2 = flank_state(c, nb, ne)
            inarc, wf = landing(tuple(sorted((c,) + nb)), c, nb)
            key = (st2[0], 'lands in the arc' if inarc else 'lands beyond the arc')
            pert[key] += 1
            if st2[0] == 'free':
                freers.append((block.index(x) + 1, dlt, 'occupant' if any(x == y for a, b, y in (st[2] if st[0] == 'handoff' else [])) else ('flank' if x == e else 'other')))
    inarc, wf = landing(S, c, block)
    return dict(block=block, e=e, rank=block.index(e) + 1, n=len(us), state=st[0], s=st[1] if st[0] == 'handoff' else None,
                segs=segs, pert=pert, freers=freers, chk=chk, lands=(inarc, wf))


if __name__ == '__main__':
    pops = [('E235 f=6', HF.gen(6, 240, 1000)[0]), ('E243 f=6', W.gen(242, 1000)[0])]
    items = []
    for name, pop in pops:
        with Pool(8) as pool:
            items += [x for part in pool.map(read_shadows, pop, chunksize=10) for x in part if not x['common']]
    with Pool(8) as pool:
        res = pool.map(study, items)
    out = open('hole6_handoff_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    ck = Counter()
    for r in res:
        ck.update(r['chk'])
    w("hand-offs read: %d; CHECKS: %s" % (len(res), dict(ck) if ck else '0 failures'))
    w("segments s per hand-off: %s" % dict(sorted(Counter(r['s'] for r in res).items())))
    seglen = Counter(); pers = Counter()
    for r in res:
        for a, b, L, rank, (A, A8, eps, p) in r['segs']:
            seglen[L] += 1
            pers['segment within its occupant\'s persistence 1/(4|eps|) + 1' if p is not None and L <= p + 1 else 'segment longer than persistence + 1'] += 1
    w("segment lengths (openings): %s" % dict(sorted(seglen.items())))
    w("segments against their occupant's persistence: %s" % dict(pers))
    w("segment occupants (A mod 8, sign of eps): %s" % dict(Counter((A8, '+' if eps > 0 else '-') for r in res for a, b, L, rank, (A, A8, eps, p) in r['segs'])))
    tot = Counter()
    for r in res:
        tot.update(r['pert'])
    w("perturbations (one reading +-1, +-2): %s" % dict(tot))
    w("moves that free the flank, by the moved reading's role: %s" % dict(Counter(f[2] for r in res for f in r['freers'])))
    for r in res:
        w("\n  block %s  flank rank %d (e = %d), run %d openings, s = %s; the cascade lands in the arc: %s at flank %s" % (
            r['block'], r['rank'], r['e'], r['n'], r['s'], r['lands'][0], r['lands'][1]))
        for a, b, L, rank, desc in r['segs']:
            w("     openings %d-%d (%d): walker rank %d, (A, A mod 8, eps, 1/(4|eps|)) = %s" % (a, b, L, rank, desc))
        w("     perturbations: %s; freeing moves (rank, delta, role): %s" % (dict(r['pert']), r['freers']))
    out.close()
    print(open('hole6_handoff_v1.out').read()[len(__doc__):][:7000])
