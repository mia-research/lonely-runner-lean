"""E252/E253 (2026-10-01): phase 3c.  The f = 6 case at the block flanks, openings only.  Design: log E252.

Population: the E235 and E243 f = 6 configurations not settled by K0 (block clear at c's exit).  First, E60
(lonely_of_off_lattice): a reading not divisible by the gcd h > 1 of the other six closes the set; recorded and set aside.
At each block flank e, c's band run: openings u = 8k + 1 with e/c <= u <= 7e/c (c reads c u / e in [1, 7]).  At each
opening of the run, walker x_j (a block reading other than e) reads x_j u / e; in the way iff x_j u mod 8e is outside
[e, 7e] (Theorem 6.14).  Per flank: the first opening of the run with no walker in the way (its index), or shadowed across
the run; at every opening before it, the walkers in the way with reading mod 8, reduced denominator q of x_j/e, and
ghat = min(frac(x_j/e), 1 - frac(x_j/e)).
Checks: c is never in the way inside its run (Theorem 6.18's bad-run bound, R4); the earliest first-clear opening over the
flanks is the cascade's landing; the full set is lonely there.
"""
import sys, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8
import holef_cascade_v1 as HF, hole6_wide_v1 as W


def lonely(S, t):
    return all(cd(d * t) >= E8 for d in S)


def e60(S):
    out = []
    for x in S:
        g = 0
        for y in S:
            if y != x:
                g = math.gcd(g, y)
        if g > 1 and x % g:
            out.append((x, g))
    return out


def inway(x, u, e):
    r = (x * u) % (8 * e)
    return r < e or r > 7 * e


def study(cb):
    core, block = cb
    c = core[0]; S = tuple(sorted(core + block))
    if lonely(S, F(1, 8 * c)):
        return None
    chk = Counter()
    off = e60(S)
    flanks = []
    for e in block:
        k0 = math.ceil((F(e, c) - 1) / 8); k1 = math.floor((F(7 * e, c) - 1) / 8)
        first = None; blocked = []
        for k in range(k0, k1 + 1):
            u = 8 * k + 1
            if inway(c, u, e):
                chk['c in the way inside its run'] += 1
            ins = [x for x in block if x != e and inway(x, u, e)]
            if not ins:
                first = k - k0; break
            blocked.append([(block.index(x) + 1, round(float(F(x * u, e) % 8), 3), e // math.gcd(x, e),
                             round(float(min(F(x, e) % 1, 1 - F(x, e) % 1)), 4)) for x in ins])
        flanks.append(dict(e=e, rank=block.index(e) + 1, nrun=k1 - k0 + 1, first=first, blocked=blocked,
                           t=F(8 * (k0 + first) + 1, 8 * e) if first is not None else None))
    clear = [f for f in flanks if f['t'] is not None]
    ts, _ = trace(S)
    if not clear or min(f['t'] for f in clear) != ts:
        chk['earliest first-clear is not the cascade landing'] += 1
    elif not lonely(S, ts):
        chk['not lonely at the landing'] += 1
    return dict(core=core, block=block, chk=chk, off=off, flanks=flanks)


def summarise(w, name, res):
    ck = Counter()
    for r in res:
        ck.update(r['chk'])
    w("\n== %s: %d configurations not settled by K0 ==" % (name, len(res)))
    w("  CHECKS: %s" % (dict(ck) if ck else '0 failures'))
    off = [r for r in res if r['off']]
    w("  closed by E60 (lonely_of_off_lattice; a reading not divisible by the gcd of the other six): %d" % len(off))
    w("     which reading and which gcd (first 10): %s" % [(r['block'], r['off'][:2]) for r in off[:10]])
    gen = [r for r in res if not r['off']]
    w("  left (every six coprime): %d" % len(gen))
    nsh = Counter(sum(1 for f in r['flanks'] if f['first'] is None) for r in gen)
    w("  flanks shadowed across c's band run, per configuration: %s" % dict(sorted(nsh.items())))
    blk = [op for r in gen for f in r['flanks'] for op in f['blocked'] if f['first'] is not None]
    w("  blocked openings before a flank's first clear one: %d; walkers in the way per opening: %s" % (
        len(blk), dict(sorted(Counter(len(op) for op in blk).items()))))
    qs = Counter(); gh = Counter()
    for op in blk:
        for rank, rd, q, g in op:
            qs['q <= 16' if q <= 16 else ('q <= 1000' if q <= 1000 else 'q > 1000')] += 1
            gh[int(10 * g) / 10] += 1
    w("  those blockers: reduced denominator of x_j/e: %s; ghat (tenths): %s" % (dict(qs), dict(sorted(gh.items()))))
    sh = [(r, f) for r in gen for f in r['flanks'] if f['first'] is None]
    w("  shadowed flanks (%d): run length in openings by rank of the flank: %s" % (len(sh), dict(sorted(Counter((f['rank'], f['nrun']) for r, f in sh).items()))))
    for r, f in sh[:25]:
        walkers = sorted({(rank, q, g) for op in f['blocked'] for rank, rd, q, g in op})
        w("    block %s flank rank %d (e = %d), run of %d openings; shadowing walkers (rank, q, ghat): %s; max ghat %.3f" % (
            r['block'], f['rank'], f['e'], f['nrun'], walkers, max(g for rank, q, g in walkers)))
        w("       per opening (blockers as (rank, reading mod 8)): %s" % [[(rank, rd) for rank, rd, q, g in op] for op in f['blocked'][:12]])


if __name__ == '__main__':
    pops = [('E235 f=6 (ratios below 2)', HF.gen(6, 240, 1000)[0]), ('E243 f=6 (some ratio 2 to 9)', W.gen(242, 1000)[0])]
    out = open('hole6_shadow_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    for name, pop in pops:
        with Pool(8) as pool:
            res = [r for r in pool.map(study, pop, chunksize=10) if r]
        summarise(w, name, res)
    out.close()
    print(open('hole6_shadow_v1.out').read()[len(__doc__):])
