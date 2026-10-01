"""E254/E255 (2026-10-01): do the lower orders' template at order eight (v21 17C, OrderEightCasesN) and E60
(lonely_of_off_lattice) reach the hole configurations?  Design: log E254.

Field implementations copied from experiments/nN/eight_residual_count_v5.py and v6.py (those scripts run on import).
For each configuration (seven whole-number disparities: the core and the block), the first 17C rule whose condition
holds, in EightResidual's field order, then E60; the configurations in EightResidual that E60 does not close are listed.
Check: the full set is lonely at the small-resolution instant (8j+1)/(8D) and at band certificates when those rules fire.
"""
import sys, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
from quantity_tests_v1 import cd, E8
import hole3_cascade_v1 as H3, holef_cascade_v1 as HF, hole6_wide_v1 as W


def free_flank8(S, e):
    for d in S:
        if d != e and d % 8 == 0:
            r = d % (8 * e)
            if not (e <= r <= 7 * e): return False
    for k in range(8):
        if all((d * k + d // e) % 8 not in (0, 7) for d in S if d % 8): return True
    return False

def shifted(S):
    e = max(S)
    if e % 8: return False
    if any(d % 8 == 0 for d in S if d != e): return False
    return sum(1 for d in S if d != e and d % 2) <= 3

def first_lap(S):
    for e in S:
        others = [d for d in S if d != e]
        lo, hi = min(others), max(others)
        A = 1
        while hi * A <= 7 * e:
            if lo * A >= e: return True
            A += 8
    return False

def minus_seven(S):
    return any(all(e <= (-7 * d) % (8 * e) <= 7 * e for d in S) for e in S)

def rational_opening(S, N, M, i):
    for d in S:
        c = (8 * (i * d % N) + d // M) % (8 * N)
        if not (N <= c and (c < 7 * N or (c == 7 * N and d % M == 0))): return False
    return True

def has_N(S, Ns):
    return any(rational_opening(S, N, e // N, i) for e in S for N in Ns if e % N == 0 for i in range(N))

def clears(S, D, a): return all(D <= d * a % (8 * D) <= 7 * D for d in S)

def small_res(S, cap=64):
    for D in range(1, cap + 1):
        for j in range(D):
            if clears(S, D, 8 * j + 1): return (D, j)
    return None

def e60(S):
    for x in S:
        g = 0
        for y in S:
            if y != x: g = math.gcd(g, y)
        if g > 1 and x % g: return (x, g)
    return None

def lonely(S, t):
    return all(cd(d * t) >= E8 for d in S)

def classify(S):
    S = tuple(sorted(S)); chk = Counter()
    if math.gcd(*S) > 1: return 'common factor', chk
    for q in (5, 6, 7, 8):
        if not any(d % q == 0 for d in S): return 'R6 q=%d' % q, chk
    if not S[-1] > 7 * S[0]: return 'R1 spread', chk
    if sum(4 if d % 8 == 4 else 2 for d in S if d % 8) < 8: return 'descent', chk
    if any(free_flank8(S, e) for e in S if e % 8 == 0): return 'free flank', chk
    if shifted(S): return 'R4 shifted', chk
    if S[-1] > 7 * S[-2]: return 'R8 fast', chk
    if first_lap(S): return 'first lap', chk
    if minus_seven(S): return 'minus seven', chk
    if has_N(S, (1, 2, 4, 8)): return 'rational opening', chk
    if has_N(S, (3,)): return 'thirds', chk
    if has_N(S, (5,)): return 'fifths', chk
    if has_N(S, (6, 7, 9)): return 'sixths/sevenths/ninths', chk
    sr = small_res(S)
    if sr:
        D, j = sr
        if not lonely(S, F(8 * j + 1, 8 * D)): chk['small resolution instant not lonely'] += 1
        return 'small resolution D=%d' % D if D <= 8 else 'small resolution D in 9..64', chk
    if e60(S): return 'E60 off-lattice', chk
    return 'EightResidual, not E60', chk

def one(cb):
    core, block = cb
    return classify(tuple(core) + tuple(block)), tuple(core) + tuple(block)

if __name__ == '__main__':
    pops = [('f=3 (E233)', H3.gen(232, 2000))] + [('f=%d (E235)' % f, HF.gen(f, 234 + f, 1000)[0]) for f in (4, 5, 6)] + [('f=6 wide (E243)', W.gen(242, 1000)[0])]
    out = open('hole_residual_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    for name, pop in pops:
        with Pool(8) as pool:
            res = pool.map(one, pop, chunksize=20)
        ck = Counter()
        for (rule, c), S in res:
            ck.update(c)
        w("\n== %s: %d configurations ==" % (name, len(res)))
        w("  CHECKS: %s" % (dict(ck) if ck else '0 failures'))
        w("  first rule that holds: %s" % dict(Counter(rule for (rule, c), S in res).most_common()))
        left = [S for (rule, c), S in res if rule == 'EightResidual, not E60']
        w("  in EightResidual and not closed by E60 (%d), first 15: %s" % (len(left), left[:15]))
    out.close()
    print(open('hole_residual_v1.out').read()[len(__doc__):])
