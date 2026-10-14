"""E393 (2026-10-05), shape43_freeedge_v1: the free-edge forward move on the residual shape (4 multiples of 8, 3 non-multiples).

Owner: "Ok" (to the plan: state the rule, prove it by hand, test the coverage on shape (4,3), perturb what it leaves).
SHAPE (4,3) of MANUSCRIPT_v22 section 17C: seven positive whole numbers, exactly four multiples of 8 (8E_1 < ... < 8E_4) and three
non-multiples c_1, c_2, c_3; overall gcd 1; at least one odd; cost sum over non-multiples of max(2, gcd(c,8)) >= 8 (so one c is 4 mod 8).
RULE (free-edge forward/backward move), hypotheses and conclusion, stated before the run:
  Fix a class a in {1,3,5,7} and a direction d in {+1,-1}.  Let tau* = the least tau > 0 at which the cofactors E_1..E_4 are all at
  distance >= 1/8 from the integers (the order-five problem, margin 1/5) and s* = tau*/8.  Put t = a/8 + d s*.
  (H1) edge condition: no non-multiple c has (a c) mod 8 = 7 when d = +1, or = 1 when d = -1 (the edge the move would push into the slot);
  (H2) room: every non-multiple c at residue r = (a c) mod 8 satisfies r/8 + d c s* in [1/8, 7/8] (so position stays in the band, no wrap).
  CONCLUSION: the subject is lonely at t.  PROOF (by hand): a multiple 8E_i at t = a/8 + d s* sits at E_i a + 8E_i d s*, i.e. at
  distance ||8E_i s*|| from the integers (the whole lap E_i a is invisible), which is >= 1/8 by the choice of tau* = 8 s*; a
  non-multiple c sits at (a c)/8 + d c s*, whose distance from the integers is >= 1/8 by (H2).  (H1) is only a guard: it is implied by
  (H2) at residue 7 or 1 when d c s* has the wrong sign, and is kept to name the failure.
RECORDED (exact, Fractions): over every such set with readings <= 48: the sets with some (a, d) satisfying H1; the sets with some
(a, d) satisfying H1 and H2 (the rule applies); the leftover (no (a, d) satisfies H2).  For the leftover: the least reading of the
multiples against the largest non-multiple, to name the failing room.  Misses of the rule's conclusion (H1, H2 hold and the exact
cascade says not lonely at t) are listed; none predicted.
"""
import itertools, math, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
import deform_pinch_v1 as D
from quantity_tests_v1 import cd, E8

def cost(c):
    return max(2, math.gcd(c, 8))

def work(chunk):
    out = []
    for Ms, ns in chunk:
        S = list(Ms) + list(ns)
        g = 0
        for x in S: g = math.gcd(g, x)
        if g != 1 or not any(x % 2 for x in ns) or sum(cost(c) for c in ns) < 8:
            continue
        Es = [F(m // 8) for m in Ms]
        tau = D.cascade_landing(Es, cap=100000)
        s = tau / 8
        ok_h1 = False; ok_rule = False; miss = False; rooms = []
        for a in (1, 3, 5, 7):
            for d in (1, -1):
                t = F(a, 8) + d * s
                if t <= 0:
                    continue
                h1 = all(((a * c) % 8) != (7 if d == 1 else 1) for c in ns)
                if h1: ok_h1 = True
                h2 = True
                for c in ns:
                    r = (a * c) % 8
                    pos = F(r, 8) + d * c * s
                    if not (F(1, 8) <= pos <= F(7, 8)):
                        h2 = False
                if h1 and h2:
                    ok_rule = True
                    lon = all(cd(F(x) * t) >= E8 for x in S)
                    if not lon:
                        miss = True
        out.append((tuple(Ms), tuple(ns), ok_h1, ok_rule, miss, tau))
    return out

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 48
    mults = [m for m in range(8, N + 1, 8)]
    non = [c for c in range(1, N + 1) if c % 8]
    items = [(Ms, ns) for Ms in itertools.combinations(mults, 4) for ns in itertools.combinations(non, 3)]
    chunks = [items[i:i + 2000] for i in range(0, len(items), 2000)]
    with Pool(4) as pool:
        res = [r for c in pool.map(work, chunks) for r in c]
    out = open('shape43_freeedge_v1.out', 'w'); out.write(__doc__ + "\n")
    n = len(res); h1 = sum(1 for r in res if r[2]); rule = sum(1 for r in res if r[3]); miss = [r for r in res if r[4]]
    out.write("readings <= %d: shape (4,3) sets passing the first fields %d; some (a,d) with H1: %d; the rule applies (H1 and H2): %d; leftover: %d; conclusion misses: %d\n" % (N, n, h1, rule, n - rule, len(miss)))
    left = [r for r in res if not r[3]]
    c = Counter()
    for Ms, ns, a, b, m, tau in left:
        c[(min(Ms), max(ns) > min(Ms))] += 1
    out.write("leftover by (least multiple, largest non-multiple above the least multiple): %s\n" % dict(sorted(c.items())))
    for r in left[:12]:
        out.write("  leftover example: multiples %s non-multiples %s tau* = %s\n" % (r[0], r[1], r[5]))
    for r in miss[:12]:
        out.write("  MISS: %s %s\n" % (r[0], r[1]))
    out.close(); print(open('shape43_freeedge_v1.out').read()[len(__doc__):][:3000])
