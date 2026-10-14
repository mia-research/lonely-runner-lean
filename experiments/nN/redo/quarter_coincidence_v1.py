"""E426 (2026-10-07), quarter_coincidence_v1: the quarter level with two odd readings made to coincide.  Exact.
Derived (by hand): at the four instants t + j/4 (j = 0..3) a reading divisible by 4 is unchanged (a(t + j/4) = at +
(a/4)j); an odd reading w sits at four points spaced 1/4 apart and blocks at most one j.  For two odd readings with
w_i = +-w_j (mod 4), 4h = |w_i -+ w_j|: at t = m/(4h) the difference (or sum) times t + j/4 is a whole number for every j,
so w_i and w_j sit at the same (or mirror) points and block the same j.  So with exactly four odd readings, no reading
= 2 (mod 4), and every multiple of 4 clear at t, at most three j are blocked and S is lonely at some t + j/4
[PROVISIONAL: counting tool; supports: the free quarter instant].  The search here: for each pair, m = 1..4h-1, the
first m with every multiple of 4 clear at m/(4h); then the exact check of S at m/(4h) + j/4.
Populations: (a) every 7-subset of [1, N] with three multiples of 8 and four odd readings (shape (3,4), type
(o,o,o,o)), gcd 1; (b) the divisible members of divisible_members_v2.json (shape (3,4), (o,o,o,o)).
Recorded: settled by some pair (with the pair's h), and the sets left.
"""
import sys, json, itertools, math, collections
from math import gcd
from functools import reduce
from fractions import Fraction as F
def cd(x): x = x - math.floor(x); return min(x, 1 - x)
E8 = F(1, 8)
def lonely(S, t): return all(cd(d * t) >= E8 for d in S)
def clear_frac(a, p, q):          # ||a p/q|| >= 1/8, integers
    r = (a * p) % q; return 8 * r >= q and 8 * (q - r) >= q
def quarter_pair(S, CAP=10**6):
    still = [d for d in S if d % 4 == 0]; odd = [d for d in S if d % 2]
    if any(d % 4 == 2 for d in S) or len(odd) != 4: return None
    for wi, wj in itertools.combinations(odd, 2):
        s = wi - wj if (wi - wj) % 4 == 0 else wi + wj
        h = abs(s) // 4
        if h == 0: continue
        for m in range(1, min(4 * h, CAP)):
            if all(clear_frac(a, m, 4 * h) for a in still):
                t = F(m, 4 * h)
                for j in range(4):
                    if lonely(S, t + F(j, 4)): return (wi, wj, h, t + F(j, 4))
                return ('FAIL: grid point found, no free quarter', wi, wj, h, t)
    return False
if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    out = open('quarter_coincidence_v1.out', 'w'); out.write(__doc__ + "\n")
    c = collections.Counter(); left = []; fails = []
    mults = list(range(8, N + 1, 8)); odds = list(range(1, N + 1, 2))
    for M in itertools.combinations(mults, 3):
        for W in itertools.combinations(odds, 4):
            S = M + W
            if reduce(gcd, S) > 1: continue
            r = quarter_pair(S); c['sets'] += 1
            if r is None: continue
            if r is False: c['left'] += 1; left.append(S)
            elif isinstance(r[0], str): c['FAIL'] += 1; fails.append((S, r))
            else: c['settled'] += 1
    out.write("(a) every 7-subset of [1,%d], three multiples of 8, four odd, gcd 1: %s\n" % (N, dict(c)))
    out.write("    failures (grid point with no free quarter instant): %d %s\n" % (len(fails), fails[:3]))
    out.write("    left (no pair has a grid point clear for the multiples): %d %s\n" % (len(left), left[:20]))
    store = json.load(open('divisible_members_v2.json')); c2 = collections.Counter(); left2 = []; fails2 = []; hs = collections.Counter()
    for k in ('A', 'B'):
        for S in store[k]:
            r = quarter_pair(tuple(S)); c2[(k, 'sets')] += 1
            if r is False: c2[(k, 'left')] += 1; left2.append(S)
            elif r is None: c2[(k, 'not the pattern')] += 1
            elif isinstance(r[0], str): c2[(k, 'FAIL')] += 1; fails2.append((S, r))
            else: c2[(k, 'settled')] += 1; hs[min(r[2], 10**9)] += 0
    out.write("(b) divisible members: %s; failures %d; left %d\n" % (dict(c2), len(fails2), len(left2)))
    out.close(); print(open('quarter_coincidence_v1.out').read()[len(__doc__):])
