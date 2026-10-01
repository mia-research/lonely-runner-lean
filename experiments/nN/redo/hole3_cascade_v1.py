"""E232/E233 (2026-10-01): the cascade inside the hole ArrBlockRule8 3 9, read move by move.  Design: log E232.

A core of four (c1 < c2 < c3 < c4 = m) below a block of three (x1 < x2 < x3, x1 >= 9m), less every block-level rule
already proved (fast pair, R8, block split, nested windows with the core at 1/5).  Map run: no window, no bound.
Read per path: the core's own first isolation tau_C and its lonely cells; the landing t*; which core cell holds t*;
the setters in order (C core / B block) with laps; the block's positions at tau_C; the last move's setter and queue front.
Checks: C1 (t* = least clear point, no cascade); t* >= tau_C; t* in a core cell.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8


def need_t(L):
    n = F(0)
    for a in reversed(L):
        if a * n > F(3, 4):
            return None
        n = 2 * n + F(1, 4 * a)
    return n


def nested_covers(core, block):
    m = max(core); best = None
    for p in itertools.permutations(block):
        n = need_t(list(p))
        if n is not None and (best is None or n < best):
            best = n
    return best is not None and best <= F(3, 20 * m)


def gen(seed, n):
    rng = random.Random(seed); out = []
    while len(out) < n:
        m = 1000
        core = sorted({int(round(m * rng.uniform(0.05, 1))) for _ in range(3)} | {m})
        if len(core) != 4:
            continue
        x1 = int(round(m * rng.uniform(9, 35 / 3)))
        x2 = int(round(x1 * rng.uniform(1, 2))); x3 = int(round(x2 * rng.uniform(1, 2)))
        block = [x1, x2, x3]
        if len(set(block)) < 3 or x1 < 9 * m:
            continue
        if x2 >= 9 * x1 or x3 >= 7 * x2 or math.gcd(math.gcd(x1, x2), x3) >= 28 * m:
            continue
        if nested_covers(core, block):
            continue
        out.append((tuple(core), tuple(block)))
    return out


def study(args):
    core, block = args
    S = tuple(sorted(core + block)); c1 = core[0]
    tc, cmoves = trace(core)
    ts, moves = trace(S)
    chk = Counter()
    least = clear_set([F(d, c1) for d in S], F(1), max(F(40), 8 * c1 * ts + 1))[0][0]
    if least != 8 * c1 * ts:
        chk['C1'] += 1
    if ts < tc:
        chk['t* < tau_C'] += 1
    Rlo, Rhi = 8 * c1 * tc, 8 * c1 * ts
    cells = clear_set([F(d, c1) for d in core], Rlo, Rhi + 1)
    idx = next((i for i, (a, b) in enumerate(cells) if a <= Rhi <= b), None)
    if idx is None:
        chk['t* not in a core cell'] += 1
    seq = []
    for t, way, st, nx in moves:
        h = min(st); K = (8 * h * nx - 1) / 8
        seq.append(('C' if h in core else 'B', int(K)))
    pat = ''.join(s for s, k in seq)
    insts = [mv[0] for mv in moves] + [ts]
    passes = tc in insts
    bpos = tuple(sorted(float((8 * x * tc) % 8) for x in block))
    b_in_way_at_tc = sum(1 for x in block if cd(x * tc) < E8)
    core_in_way_at_ts_minus = None
    last = moves[-1] if moves else None
    last_setter = ('C' if min(last[2]) in core else 'B') if last else 'bound'
    return dict(core=core, block=block, chk=chk, tc=tc, ts=ts, ratio=float(ts / tc), cell=idx, pat=pat, passes=passes,
                bpos=bpos, b_in_way=b_in_way_at_tc, last=last_setter, nmoves=len(moves),
                pre=[s for t_, s in zip(insts, pat) if t_ < tc], post=[s for t_, s in zip(insts, pat) if t_ >= tc])


def rle(p):
    out = []
    for ch in p:
        if out and out[-1][0] == ch:
            out[-1][1] += 1
        else:
            out.append([ch, 1])
    return ' '.join('%s%d' % (c, n) for c, n in out)


if __name__ == '__main__':
    pop = gen(232, 2000)
    with Pool(8) as pool:
        rows = pool.map(study, pop, chunksize=25)
    out = open('hole3_cascade_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    ck = Counter()
    for r in rows:
        ck.update(r['chk'])
    w("\n== the hole ArrBlockRule8 3 9 less the proved block rules: %d configurations ==" % len(rows))
    w("  CHECKS (C1; t* >= tau_C; t* in a core cell): %s" % (dict(ck) if ck else '0 failures'))
    w("  t* equals tau_C: %d" % sum(1 for r in rows if r['ts'] == r['tc']))
    w("  core cell holding t* (0 = the cell starting at tau_C): %s" % dict(sorted(Counter(r['cell'] for r in rows).items())))
    w("  t*/tau_C: <=1.0 %d; (1,1.25] %d; (1.25,1.5] %d; (1.5,2) %d; >=2 %d" % tuple(
        sum(1 for r in rows if lo < r['ratio'] <= hi) for lo, hi in ((0, 1.0), (1.0, 1.25), (1.25, 1.5), (1.5, 1.999999), (1.999999, 1e9))))
    w("  the path passes through tau_C: %d of %d" % (sum(r['passes'] for r in rows), len(rows)))
    w("  block readings in the way at tau_C: %s" % dict(sorted(Counter(r['b_in_way'] for r in rows).items())))
    w("  setters before tau_C: %s" % dict(Counter(''.join(sorted(set(r['pre']))) or 'none' for r in rows)))
    w("  setters at or after tau_C: %s" % dict(Counter(''.join(sorted(set(r['post']))) or 'none' for r in rows)))
    w("  last setter: %s" % dict(Counter(r['last'] for r in rows)))
    w("  moves: %s" % dict(sorted(Counter(r['nmoves'] for r in rows).items())))
    w("  path patterns (run-length), most common: %s" % Counter(rle(r['pat']) for r in rows).most_common(15))
    odd = [r for r in rows if r['cell'] != 0]
    w("  paths landing beyond the core's first cell (%d), listed:" % len(odd))
    for r in odd[:30]:
        w("    core %s block %s  t*/tau_C %.4f cell %s  pattern %s  block positions at tau_C %s" %
          (r['core'], r['block'], r['ratio'], r['cell'], rle(r['pat']), tuple(round(p, 3) for p in r['bpos'])))
    out.close()
    print(open('hole3_cascade_v1.out').read()[len(__doc__):])
