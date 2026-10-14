"""The 14 exceptions: sharer flank shadowed with no runner at ratio denominator 2 or 4 to the sharer. Print differences, the
shared flank e, m, every runner's ratio to e and to s, and the smallest blocking set."""
import itertools
from fractions import Fraction as F
from flank_near_extreme_v1 import blocks_all
n = 8
for v in itertools.combinations(range(1, 21), n):
    for i in range(n):
        ds = [abs(x - v[i]) for x in v if x != v[i]]
        flanks = sorted(set(ds))
        for s in flanks:
            for e in flanks:
                if s == e or s % (n * e): continue
                others = [d for d in ds if d != s]
                if not blocks_all(s, others, n): continue
                if {F(d, s).denominator for d in others} & {2, 4}: continue
                best = None
                for size in range(1, len(others) + 1):
                    for S in itertools.combinations(others, size):
                        if blocks_all(s, list(S), n): best = S; break
                    if best: break
                print(f'speeds {v} subject {v[i]} differences {sorted(ds)}; e={e}, s={s} (m={s//(n*e)})')
                print(f'   ratios to e: {[str(F(d, e)) for d in sorted(others)]}; smallest blocking set {best} with ratios to s {[str(F(d, s)) for d in best]}')
