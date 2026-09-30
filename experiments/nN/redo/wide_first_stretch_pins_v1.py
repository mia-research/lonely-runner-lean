"""E212 (2026-10-01): what holds the first clear stretch open at the walk's tightest wide sets.

For each of the tightest sets of `wide_first_stretch_walk_v1` (re-run with the same seeds, keeping every walk's final
set), take the clear intervals of R in [1, 7] and, at each end of each interval, the reading at an edge (position 1 or 7
mod 8, exact).  Recorded: per set, the end-pinning pairs (reading at 7 on one end, reading at 1 on the other), their
ratio, and whether one pair pins both ends of the narrowest interval in opposite orientation (the mirror pair, E125).
"""
import sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
import wide_first_stretch_walk_v1 as W

D = W.D


def pins(T):
    s = [F(d, D) for d in T]
    S = clear_set(s, F(1), F(7))
    a, b = min(S, key=lambda iv: iv[1] - iv[0])
    at = lambda R, pos: [d for d, x in zip(T, s) if (x * R) % 8 == pos]
    left = (at(a, 1), at(a, 7)); right = (at(b, 1), at(b, 7))
    return dict(T=T, width=b - a, a=a, b=b, left=left, right=right, n_int=len(S))


if __name__ == '__main__':
    import random
    rng = random.Random(212); starts = []
    from coverB_fine_v1 import late_shapes
    L = late_shapes()
    for T in rng.sample(L, 150):
        pos = rng.randrange(1, 6); u = rng.choice((9.001, 9.05, 9.5))
        S = sorted((set(T) - {T[pos]}) | {int(u * D)})
        if len(S) == 7:
            starts.append(S)
    while len(starts) < 300:
        Wt = int(rng.uniform(9.001, 12) * D)
        S = sorted({D, Wt} | {rng.randrange(D + 1, Wt) for _ in range(5)})
        if len(S) == 7:
            starts.append(S)
    with Pool(8) as pool:
        res = pool.map(W.walk, [(k, s, 4000) for k, s in enumerate(starts)])
    tight = sorted(res)[:25]
    out = open('wide_first_stretch_pins_v1.out', 'w'); out.write(__doc__ + "\n")
    kinds = Counter()
    for b, T, _ in tight:
        p = pins(T)
        (l1, l7), (r1, r7) = p['left'], p['right']
        # the interval opens at a (a reading leaves: at 1) and closes at b (a reading enters: at 7)
        mirror = [(x, y) for x in l1 for y in r7] if p['width'] > 0 else []
        pair = sorted(set(l1) | set(l7) | set(r1) | set(r7))
        kind = 'point' if p['width'] == 0 else 'interval'
        kinds[kind] += 1
        out.write("%s width %.3g in [%s, %s] (%d clear intervals in [1,7])\n  opens: at-1 %s at-7 %s | closes: at-1 %s at-7 %s\n"
                  % (T, float(p['width']), p['a'], p['b'], p['n_int'], l1, l7, r1, r7))
        if len(pair) == 2:
            out.write("  one pair at both ends, ratio %s\n" % F(pair[1], pair[0]))
    out.write("kinds: %s\n" % dict(kinds))
    out.close()
    print(open('wide_first_stretch_pins_v1.out').read()[len(__doc__):])
