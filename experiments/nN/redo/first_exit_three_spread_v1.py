"""E239 (2026-10-01): the spread of the triples with a start at which no first exit is clear, against the spread of the
blocks left in the hole ArrBlockRule8 3 9 (after the proved rules).

(1) The f = 3 hole population (hole3_cascade_v1.gen(232, 2000)): the block's spread x3/x1, least and greatest.
(2) Exhaustive, exact, whole-number triples a < b < c <= 80 with c/a below 2.2: every start (as in first_exit_three_v1),
    and for each triple with a bad start, its spread.  The least spread of a bad triple is reported with the triple.
"""
import itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
import hole3_cascade_v1 as H3
from first_exit_three_v1 import check


def run(sets):
    return [(S, len(m), m[:2]) for S, m in (check(S) for S in sets)]


if __name__ == '__main__':
    out = open('first_exit_three_spread_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    sp = [F(b[2], b[0]) for c, b in H3.gen(232, 2000)]
    w("hole f = 3 blocks (2,000): spread x3/x1 from %.4f to %.4f; by tenth: %s" % (
        float(min(sp)), float(max(sp)), dict(sorted(Counter(int(10 * s) / 10 for s in sp).items()))))
    sets = [S for S in itertools.combinations(range(1, 81), 3) if F(S[2], S[0]) < F(11, 5)]
    with Pool(8) as pool:
        res = [x for part in pool.map(run, [sets[i::64] for i in range(64)]) for x in part]
    bad = sorted([(F(S[2], S[0]), S, ms) for S, n, ms in res if n], key=lambda x: x[0])
    w("triples <= 80 with spread below 2.2: %d; with a bad start: %d" % (len(sets), len(bad)))
    w("bad triples by spread (tenth): %s" % dict(sorted(Counter(int(10 * s) / 10 for s, S, ms in bad).items())))
    w("the 15 least-spread bad triples:")
    for s, S, ms in bad[:15]:
        w("   %s spread %.4f starts %s" % (S, float(s), [str(t) for t in ms]))
    out.close()
    print(open('first_exit_three_spread_v1.out').read()[len(__doc__):])
