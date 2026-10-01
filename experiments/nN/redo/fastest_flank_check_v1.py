"""E261/E262 (2026-10-02): a truth check of (b) from the record's theorems.  Design: log E261.

Every six-set <= 30 with gcd 1: is its largest flank e shadowed at every opening j < e (threshold 1/8; walker d in the way
iff d(8j+1) mod 8e is outside [e, 7e], Theorem 6.14; period e, Theorem 6.13)?  For each such six-set: the C1-shaped set
(1, K * six), K = ceil(9 / x1); its fastest flank across c's band run (one walker throughout, or a hand-off); the cascade's
landing (flank rank); membership of EightResidual (hole_residual_v1.classify).
Check: the residue test agrees with direct circDist evaluation at the opening instants (exact) on every flagged six-set.
"""
import sys, math, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8
from hole_C1_flanks_v1 import flank
from hole_residual_v1 import classify


def largest_shadowed(S):
    e = S[-1]
    for j in range(e):
        u = 8 * j + 1
        if not any(((d * u) % (8 * e) < e or (d * u) % (8 * e) > 7 * e) for d in S[:-1]):
            return False
    return True


def direct_check(S):
    e = S[-1]
    for j in range(e):
        t = F(8 * j + 1, 8 * e)
        if all(cd(d * t) >= E8 for d in S[:-1]):
            return False
    return True


def run(sets):
    return [S for S in sets if largest_shadowed(S)]


if __name__ == '__main__':
    sets = [S for S in itertools.combinations(range(1, 31), 6) if math.gcd(*S) == 1]
    with Pool(8) as pool:
        hits = [S for part in pool.map(run, [sets[i::64] for i in range(64)]) for S in part]
    out = open('fastest_flank_check_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    bad = sum(1 for S in hits if not direct_check(S))
    w("six-sets <= 30, gcd 1: %d; largest flank shadowed at every opening: %d; residue test vs direct evaluation disagreements: %d" % (len(sets), len(hits), bad))
    rows = Counter()
    for S in hits:
        K = -(-9 // S[0]); cl = [K * x for x in S]; T = tuple([1] + cl)
        st = flank(1, cl, cl[-1])
        ts, _ = trace(T)
        h = next(x for x in T if (8 * x * ts) % 8 == 1)
        rank = cl.index(h) + 1 if h in cl else 'c'
        rule = classify(T)[0]
        rows[(st['state'], 'lands at cluster rank %s' % rank, 'EightResidual' if rule.startswith('EightResidual') else 'closed by 17C/E60')] += 1
        w("  six %s  K %d: fastest flank across c's run: %s%s; cascade lands at cluster rank %s; %s" % (
            S, K, st['state'], ' (s = %d)' % st['s'] if st['state'] == 'handoff' else '', rank, rule))
    w("summary: %s" % dict(rows))
    out.close()
    print(open('fastest_flank_check_v1.out').read()[len(__doc__):][:6000])
