"""Isolation before and after: consecutive lonely cells and the blocked gap between them.

For each pair of consecutive lonely cells in one period (wrapping round), on the 28 hard sets of
[1,40] and 400 ordinary residual sets: whether the runner closing the first also opens the second;
how many runners' zones cover the gap; the gap in zone widths 1/(4 eR) of the closing runner; the
commonest (closing rank, next opening rank).
"""
import itertools, random
from fractions import Fraction as Fr
from collections import Counter
__file__ = __file__.replace('consecutive_cells_v1.py', 'player_census_v1.py')
src = open(__file__).read(); exec(src[:src.index("R40 = [S")])
def gap_runners(S, a, b):
    """runners whose blocked zones meet the open gap (a, b)"""
    out = set()
    for d in S:
        for k in range(0, d + 2):
            lo, hi = Fr(8 * k - 1, 8 * d), Fr(8 * k + 1, 8 * d)
            if hi > a and lo < b: out.add(d)
    return out
def study(sets, label):
    same = n = 0; nrun = Counter(); width = []; closer_rank = Counter(); pair = Counter()
    for S in sets:
        C = cells_full(S); s = sorted(S); rank = {d: s.index(d) + 1 for d in S}
        for k in range(len(C)):
            c, c2 = C[k], C[(k + 1) % len(C)]
            a, b = c['R'], c2['L'] + (1 if k + 1 == len(C) else 0)
            if b <= a: continue
            n += 1
            same += (c['eR'] == c2['eL'])
            g = gap_runners(S, a, b) if k + 1 < len(C) else gap_runners(S, a, Fr(1)) | gap_runners(S, Fr(0), c2['L'])
            nrun[min(len(g), 5)] += 1
            width.append(float((b - a) * 4 * c['eR']))          # in zone widths 1/(4 eR) of the closing runner
            pair[(rank[c['eR']], rank[c2['eL']])] += 1
    width.sort()
    print(f"{label}: {n} gaps between consecutive cells")
    print(f"   closed and reopened by the same runner (a single runner's blip): {same / n:.3f}")
    print(f"   distinct runners covering the gap: {sorted((k, round(v / n, 3)) for k, v in nrun.items())}")
    print(f"   gap length in zone widths of the closing runner: min {width[0]:.2f} median {width[len(width)//2]:.2f} 90% {width[int(.9*len(width))]:.2f}")
    print(f"   (closing rank, next opening rank), top 8: {[(k, round(v / n, 3)) for k, v in pair.most_common(8)]}")
R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
f25 = [S for S in R40 if not any(rule(S, q, free_exact) for q in range(2, 6))]
hard = [S for S in f25 if not any(rule(S, q, free_exact) for q in (6, 7, 8))]
random.seed(21); easy = random.sample([S for S in R40 if S not in set(f25)], 400)
study(hard, "28 hard"); study(easy, "400 ordinary")
