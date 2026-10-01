"""E234/E235 (2026-10-01): the cascade inside the holes ArrBlockRule8 f 9, f = 4, 5, 6, read as E232/E233 read f = 3.
Design: log E234.

A core of 7 - f readings (c1 < ... < m = 1000) below a block of f (x1 >= 9m, x1/m uniform in [9, 60], consecutive block
ratios uniform in (1, 2)), less every proved rule on every split into a slower part and a top-k part: R8, the fast pair,
the block split, the train collapse, nested windows (core of j at 1/(j+1)).  1,000 configurations per f.
Checks (forced): C1 (t* = least clear point, computed without the cascade); t* >= tau_C; t* in a core stretch;
  F1 a move made from inside a core stretch has only block setters; F2 t* is the block's own relay from the path's
  first instant inside the stretch that holds t*.
Records: landing stretch; setters by region and class; paths not passing tau_C; paths landing beyond S0, move by move;
block setters in gaps.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8
from hole3_cascade_v1 import need_t
from hole3_cascade_v2 import run_from
from hole3_cascade_v3 import region


def covered(S):
    """Which proved rule covers the 7 readings S (sorted), or None."""
    S = sorted(S); n = len(S)
    if all(7 * s < S[-1] for s in S[:-1]):
        return 'R8'
    if all(9 * c <= S[-2] for c in S[:-2]):
        return 'fast pair'
    for k in range(1, n):
        top, rest = S[n - k:], S[:n - k]
        g = 0
        for x in top:
            g = math.gcd(g, x)
        if g >= 28 * max(rest):
            return 'block split'
        if k >= 2:
            mp = max(max(rest), top[-1] - top[0])
            if top[0] >= 56 * mp:
                return 'train collapse'
    for j in range(1, n):
        core, rest = S[:j], S[j:]
        room = 2 * (F(1, j + 1) - E8) / core[-1]
        for p in itertools.permutations(rest):
            nt = need_t([F(x) for x in p])
            if nt is not None and nt <= room:
                return 'nested windows'
    return None


def gen(f, seed, n):
    rng = random.Random(seed); out = []; excl = Counter()
    while len(out) < n:
        m = 1000
        core = sorted({int(round(m * rng.uniform(0.05, 1))) for _ in range(6 - f)} | {m})
        if len(core) != 7 - f:
            continue
        x = [int(round(m * rng.uniform(9, 60)))]
        for _ in range(f - 1):
            x.append(int(round(x[-1] * rng.uniform(1, 2))))
        if len(set(x)) < f:
            continue
        rule = covered(core + x)
        if rule:
            excl[rule] += 1; continue
        out.append((tuple(core), tuple(x)))
    return out, excl


def study(args):
    core, block = args
    S = tuple(sorted(core + block)); c1 = core[0]; x1 = block[0]
    tc, _ = trace(core); ts, moves = trace(S)
    chk = Counter()
    cs = clear_set([F(d, c1) for d in S], F(1), 8 * c1 * ts + 1)
    if not cs or cs[0][0] != 8 * c1 * ts:
        chk['C1'] += 1
    if ts < tc:
        chk['t* < tau_C'] += 1
    R = lambda t: 8 * c1 * t
    cells = clear_set([F(d, c1) for d in core], R(tc), R(ts) + 400)
    k_land = region(R(ts), cells)
    if not k_land.startswith('S'):
        chk['t* not in a core stretch'] += 1
    lap = lambda t: float((t - tc) * x1)
    rows = []
    for t, way, st, nx in moves:
        reg = region(R(t), cells); cls = 'C' if min(st) in core else 'B'
        if reg.startswith('S') and cls == 'C':
            chk['F1'] += 1
        rows.append((lap(t), reg, cls, min(st), tuple(d for d in way if d in core), tuple(d for d in way if d in block), lap(nx), region(R(nx), cells)))
    insts = [mv[0] for mv in moves] + [ts]
    entry = next(t for t in insts if region(R(t), cells) == k_land)
    if run_from(block, entry) != ts:
        chk['F2'] += 1
    a0, b0 = cells[0]
    return dict(core=core, block=block, chk=chk, rows=rows, k_land=k_land, passes=tc in insts, at_tc=(ts == tc),
                LC=float((b0 - a0) / (8 * c1) * x1), gB=float((run_from(block, tc) - tc) * x1), x1m=x1 / max(core),
                cells=[(round(float((a - R(tc)) / (8 * c1) * x1), 4), round(float((b - R(tc)) / (8 * c1) * x1), 4)) for a, b in cells[:3]])


def dump(w, r):
    w("core %s block %s  x1/m %.2f  stretches (laps of x1 from tau_C) %s  lands in %s" % (r['core'], r['block'], r['x1m'], r['cells'], r['k_land']))
    for x in r['rows']:
        w("   from %+.4f [%s]  setter %s %d  in the way C%s B%s  -> %+.4f [%s]" % x)


if __name__ == '__main__':
    out = open('holef_cascade_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    for f in (4, 5, 6):
        pop, excl = gen(f, 234 + f, 1000)
        with Pool(8) as pool:
            res = pool.map(study, pop, chunksize=10)
        ck = Counter()
        for r in res:
            ck.update(r['chk'])
        w("\n==================== f = %d: %d configurations (core of %d) ====================" % (f, len(res), 7 - f))
        w("excluded while sampling, by the first proved rule found: %s" % dict(excl))
        w("x1/m of the kept: %s" % dict(sorted(Counter(int(r['x1m'] // 10) * 10 for r in res).items())))
        w("CHECKS (C1, t* >= tau_C, t* in a core stretch, F1, F2): %s" % (dict(ck) if ck else '0 failures'))
        w("t* equals tau_C: %d" % sum(r['at_tc'] for r in res))
        w("landing stretch: %s" % dict(sorted(Counter(r['k_land'] for r in res).items())))
        w("moves by (from-region, setter class): %s" % dict(sorted(Counter((x[1], x[2]) for r in res for x in r['rows']).items())))
        w("block moves inside the landing stretch: %s" % dict(sorted(Counter(sum(1 for x in r['rows'] if x[1] == r['k_land']) for r in res).items())))
        w("S0 length in laps of x1 (landing in S0 / beyond): min %.4f / max %.4f" % (
            min([r['LC'] for r in res if r['k_land'] == 'S0'] or [float('nan')]), max([r['LC'] for r in res if r['k_land'] != 'S0'] or [float('nan')])))
        w("block relay from tau_C in laps of x1: max %.4f" % max(r['gB'] for r in res))
        grpB = [r for r in res if any(x[1].startswith('gap') and x[2] == 'B' for x in r['rows'])]
        for name, grp in (("landing beyond S0", [r for r in res if r['k_land'] != 'S0']),
                          ("not passing through tau_C", [r for r in res if not r['passes']]),
                          ("a block setter in a gap", grpB)):
            w("\n-- %s: %d paths (first 12 read in full) --" % (name, len(grp)))
            for r in grp[:12]:
                dump(w, r)
    out.close()
    print(open('holef_cascade_v1.out').read()[len(__doc__):][:9000])
