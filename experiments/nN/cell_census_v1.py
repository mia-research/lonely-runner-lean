"""A census of lonely cells, each with the flank that opens it, its rung, and the flank that closes it.

Integer disparities, one period (0, 1).  The blocked zones of d are ((8k-1)/(8d), (8k+1)/(8d)); the
lonely set is the complement of their union, a union of closed cells [L, R] with L an opening
(8j+1)/(8e_L) and R a closing (8k-1)/(8e_R).  The opening's rung: L = i/N + 1/(8e_L),
N = e_L/gcd(j, e_L).  At the ideal each global instant is a cell of width zero, opened by aD and
closed by (8-a)D; t -> 1 - t swaps opening and closing flanks, for every cell.

Reports, on the v1 residual of [1,30]: cells per set; opening and closing flanks by rank; the
commonest (opening rank, closing rank) pairs; the rung N of the openings.
"""
import itertools, time, random
from fractions import Fraction as Fr
from collections import Counter
from math import gcd
_rs = __file__.replace('cell_census_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
def cells(S):
    """all lonely cells [L, R] in (0, 1): L an opening of flank eL, R a closing of flank eR (exact)"""
    zones = []
    for d in S:
        for k in range(0, d + 1):
            zones.append((Fr(8 * k - 1, 8 * d), Fr(8 * k + 1, 8 * d), d, k))
    zones.sort()
    out = []; cur_hi = Fr(-1); cur_d = None; cur_k = None
    for lo, hi, d, k in zones:
        if lo >= cur_hi and cur_hi > 0 and lo < 1:      # a gap [cur_hi, lo]: closed cell (touching zones leave a point cell)
            out.append((cur_hi, cur_d, cur_k, lo, d, k))
        if hi > cur_hi: cur_hi, cur_d, cur_k = hi, d, k
    return out
def rung_of(e, j):          # opening (8j+1)/(8e): i/N + 1/(8e), N = e/gcd(j, e)
    g = gcd(j, e); return e // g, j // g
R = [S for S in itertools.combinations(range(1, 31), 7) if eight_residual(S)]
t0 = time.time(); ncell = Counter(); pairrank = Counter(); openrank = Counter(); closerank = Counter(); Nopen = Counter(); sums = Counter(); same = 0; tot = 0
for S in R:
    C = cells(S); ncell[min(len(C), 12)] += 1
    s = sorted(S); rank = {d: s.index(d) + 1 for d in S}
    for L, eL, jL, Rr, eR, kR in C:
        tot += 1
        openrank[rank[eL]] += 1; closerank[rank[eR]] += 1; pairrank[(rank[eL], rank[eR])] += 1
        N, i = rung_of(eL, jL); Nopen[min(N, 13)] += 1
        same += (eL == eR)
print(f"[1,30] residual v1 {len(R)} sets, {tot} lonely cells in (0,1)  ({time.time()-t0:.0f}s)")
print("  cells per set:", sorted(ncell.items()))
print("  opening flank by rank:", sorted(openrank.items()), "  closing flank by rank:", sorted(closerank.items()))
print("  same flank opens and closes:", same)
print("  most common (opening rank, closing rank):", pairrank.most_common(12))
print("  rung N of the opening (13 = 13 or more):", sorted(Nopen.items()))
