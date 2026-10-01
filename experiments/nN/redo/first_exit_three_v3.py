"""E239 (2026-10-01): every triple with spread below 1.62 that fails P2 (first_exit_three_v2), listed, to read its shape.

first_exit_three_v2.out shows the least-spread failing triples as near-pairs (a, a+1) with a third reading near 1.57-1.61a.
Exhaustive, exact, every triple with c <= 160 and c/a below 1.62: each failing triple with b - a, c/a, c/b and a failing
start.  Reported: the failing triples by b - a.
"""
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from first_exit_three_v2 import check


def run(sets):
    return [x for x in (check(S) for S in sets) if x[2]]


if __name__ == '__main__':
    sets = [(a, b, c) for c in range(3, 161) for a in range(1, c) if F(c, a) < F(81, 50) for b in range(a + 1, c)]
    with Pool(8) as pool:
        bad = [x for part in pool.map(run, [sets[i::256] for i in range(256)]) for x in part]
    bad.sort(key=lambda x: F(x[0][2], x[0][0]))
    out = open('first_exit_three_v3.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    w("triples with c <= 160 and spread below 1.62: %d; failing P2: %d" % (len(sets), len(bad)))
    w("failing triples by b - a: %s" % dict(sorted(Counter(x[0][1] - x[0][0] for x in bad).items())))
    for (a, b, c), p1, p2, w1, w2 in bad:
        w("   (%d, %d, %d)  b-a %d  c/a %.4f  c/b %.4f  failing starts %d, first %s" % (a, b, c, b - a, c / a, c / b, p2, w2))
    out.close()
    print(open('first_exit_three_v3.out').read()[len(__doc__):])
