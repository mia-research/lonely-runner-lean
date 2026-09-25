"""The fast-pair rule with a UNIFORM core-cell constant, on the 28 hard sets.

If every five-set core C has a lonely cell at 1/8 of length >= c / max(C), then a pair (d, d') with
ratio <= 3 certifies S once (d + d') >= (2/c) * max(C): two consecutive mirror meetings K/(d + d') then
fall in that cell.  Constants: c = 1/4 (claimed in the 2026-09-25 summary, false: five_cell_floor_v1),
c = 5/32 (exhaustive floor on [1,30]), c = 1/12 (proved: order six clears at 1/6, slack 1/6 - 1/8 on
both sides).  Hard sets are read from order5_transfer_v1.out (the 28 of the [1,40] residual).
"""
import re, itertools
from fractions import Fraction as F
hard = sorted({tuple(map(int, m.group(1).split(','))) for m in
               (re.match(r'\s*\(([\d, ]+)\):', l) for l in open('order5_transfer_v1.out')) if m})
hard = [h for h in hard if len(h) == 7]
print("hard sets:", len(hard))
def best(S):
    return max(F(d + d2, max(x for x in S if x not in (d, d2)))
               for d, d2 in itertools.combinations(sorted(S), 2) if 3 * d >= d2)
vals = sorted(best(S) for S in hard)
for c, lab in [(F(1, 4), "c = 1/4 (claimed)"), (F(5, 32), "c = 5/32 (floor)"), (F(1, 12), "c = 1/12 (proved)")]:
    print(f"{lab}: needs (d+d')/max(core) >= {float(2 / c):.1f}; hard sets meeting it: {sum(v >= 2 / c for v in vals)}/{len(vals)}")
print(f"best (d+d')/max(core) over the hard sets: min {float(vals[0]):.4f}, max {float(vals[-1]):.4f}")
