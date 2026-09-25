"""R(C, e) of sync_block_v1, extended to speeds in [1,16], with the easy case separated out.

Easy case: for t < 3/(4E) all offsets e_i t lie in an arc of length < 3/4, so the gap exceeds 1/4
automatically; R then holds if C has a clear interior point below 3/(4E).  Reports how many cases
the easy case settles and whether R holds in the rest (exact, as v1).
"""
import time
from fractions import Fraction as Fr
from itertools import combinations
exec(open('sync_block_v1.py').read().split("t0 = time.time()")[0].replace("B = int(sys.argv[1]) if len(sys.argv) > 1 else 12", "B = 16"))
def easy(C, E):
    lim = Fr(3, 4 * E); z = sorted((Fr(8 * m - 1, 8 * c), Fr(8 * m + 1, 8 * c)) for c in C for m in range(c + 1))
    cur = Fr(0)
    for a, b in z:
        if a > cur and cur < lim: return True      # an open clear stretch (cur, a) starting below lim
        cur = max(cur, b)
    return False
t0 = time.time(); n = e_ok = r_ok = 0; fails = []
for f, c in ((5, 2), (6, 1)):
    for C in combinations(range(1, B + 1), c):
        for off in combinations(range(1, B + 1), f - 1):
            n += 1; e = (0,) + off
            if easy(C, e[-1]): e_ok += 1; continue
            if R_holds(C, e) is not None: r_ok += 1
            else: fails.append((C, e))
print(f"speeds in [1,{B}]: {n} cases;  easy case (C clear before 3/(4E)) {e_ok};  R by breakpoint search {r_ok};  R fails {len(fails)} {fails[:5]}  ({time.time() - t0:.0f}s)")
