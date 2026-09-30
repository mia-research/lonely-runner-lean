"""E193b (2026-09-30): the 97 exceptions of crowded_level_v1 (no a/64 lonely), read by the three questions (M3).

For each exception, exactly:
  (i)  feature: the least q <= 8 dividing no reading (R6: 1/q is lonely), and whether six readings share a factor the
       seventh lacks (`no_one_free`); whether the set meets EightResidual's positive-arithmetic fields
       (odd, no common factor, a multiple of each of 5, 6, 7, 8);
  (ii) the smallest subsets of readings whose blocked instants already cover the 56-instant grid a/64 (the readings that
       force the exception), and the grid instants i/q (q <= 12) at which the set is lonely (where its isolation is);
  (iii) same mechanism or not: whether the isolation found is a grid instant (a grid through the arrangement, another q).
"""
import itertools, math
from fractions import Fraction as F
from collections import Counter

A = [a for a in range(1, 64) if a % 8]


def blocked(d):
    return frozenset(a for a in A if not (8 <= (a * d) % 64 <= 56))


def lonely_at_frac(S, t):
    return all(min((d * t) % 1, 1 - (d * t) % 1) >= F(1, 8) for d in S)


def analyse(S):
    r6 = [q for q in range(2, 9) if all(d % q for d in S)]
    onefree = [(x, g) for x in S for g in range(2, 25)
               if all(d % g == 0 for d in S if d != x) and x % g]
    pos = dict(odd=any(d % 2 for d in S), five=any(d % 5 == 0 for d in S), six=any(d % 6 == 0 for d in S),
               seven=any(d % 7 == 0 for d in S), eight=any(d % 8 == 0 for d in S))
    B = {d: blocked(d) for d in S}
    cover = None
    for k in range(1, 8):
        cs = [c for c in itertools.combinations(S, k) if frozenset().union(*(B[d] for d in c)) == frozenset(A)]
        if cs:
            cover = (k, cs); break
    grid = [(q, i) for q in range(2, 13) for i in range(1, q) if math.gcd(i, q) == 1 and lonely_at_frac(S, F(i, q))]
    return dict(S=S, r6=r6, onefree=onefree, pos=pos, cover=cover, grid=grid)


if __name__ == '__main__':
    import crowded_level_v1 as C
    from multiprocessing import Pool
    with Pool(8) as pool:
        recs = [r for part in pool.map(C.study, range(1, 19)) for r in part]
    exc = [r['S'] for r in recs if not r['good']]
    res = [analyse(S) for S in exc]
    o = open('crowded_level_v1b.out', 'w'); o.write(__doc__ + "\n"); w = lambda s: o.write(s + "\n")
    w("exceptions: %d" % len(res))
    w("R6 applies (some q <= 8 divides no reading): %d; by least such q: %s" %
      (sum(bool(r['r6']) for r in res), dict(sorted(Counter(r['r6'][0] for r in res if r['r6']).items()))))
    w("one-free (six share a factor the seventh lacks): %d" % sum(bool(r['onefree']) for r in res))
    allpos = [r for r in res if all(r['pos'].values())]
    w("meet all of EightResidual's positive fields odd/five/six/seven/eight: %d" % len(allpos))
    w("neither R6 nor one-free: %d" % sum(1 for r in res if not r['r6'] and not r['onefree']))
    w("size of the smallest covering subset: %s" % dict(sorted(Counter(r['cover'][0] for r in res).items())))
    w("lonely at some grid instant i/q, q <= 12: %d; least q: %s" %
      (sum(bool(r['grid']) for r in res), dict(sorted(Counter(min(q for q, i in r['grid']) for r in res if r['grid']).items()))))
    w("\nper exception: readings | R6 q | one-free | positive fields missing | smallest covers | grid instants (q,i)")
    for r in res:
        miss = [k for k, v in r['pos'].items() if not v]
        w("%s | %s | %s | %s | %d: %s | %s" % (r['S'], r['r6'], r['onefree'][:2], miss, r['cover'][0],
                                                r['cover'][1][:3], r['grid'][:6]))
    o.close()
    print(open('crowded_level_v1b.out').read()[len(__doc__):][:5000])
