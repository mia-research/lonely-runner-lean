#!/usr/bin/env python3
"""Phase 2: group the 41 T6 sets by their normalised pinch. A pinch is an entering edge (speed a, lap m) and a leaving
edge (speed b, lap m'):  L = (7m+1)/(7a),  U = (7m'+6)/(7b),  delta = (7m'+6) a - (7m+1) b > 0,  U - L = delta/(7ab).
Scaling every speed by c maps (a, b, L, U) to (ca, cb, L/c, U/c), so the invariant is (a/g, m, b/g, m') with
g = gcd(a, b), and the pinch interval in normalised time g [L, U].
A speed v is in band throughout [L, U] iff 7n+1 <= 7vL and 7vU <= 7n+6 for some whole n (closed form):
  v in A(L, U) = union_n [ (7n+1)/(7L), (7n+6)/(7U) ]."""
import math
from fractions import Fraction as Fr
from collections import defaultdict
exec(open("o7_pinch_v1.py").read().split('if __name__')[0])
groups = defaultdict(list)
for S in sorted(T6):
    iv = lonely(S); L, U = max(iv, key=lambda z: z[1] - z[0])
    (i, m), (j, mp) = [(a, int(x)) for a, x in edges(S, L, 1)][0], [(a, int(x)) for a, x in edges(S, U, 6)][0]
    a, b = S[i - 1], S[j - 1]; g = math.gcd(a, b)
    delta = (7 * mp + 6) * a - (7 * m + 1) * b
    assert Fr(7 * m + 1, 7 * a) == L and Fr(7 * mp + 6, 7 * b) == U and U - L == Fr(delta, 7 * a * b)
    groups[(a // g, m, b // g, mp)].append((S, g, g * L, g * U))
print(f"{len(T6)} T6 sets in {len(groups)} normalised pinches (a/g, m, b/g, m'):")
for key, lst in sorted(groups.items(), key=lambda kv: -len(kv[1])):
    a, m, b, mp = key; d = (7 * mp + 6) * a - (7 * m + 1) * b
    gL, gU = lst[0][2], lst[0][3]
    assert all(x[2] == gL and x[3] == gU for x in lst)
    print(f"  in ({a}, lap {m}) out ({b}, lap {mp}): delta {d}, g[L,U] = [{gL}, {gU}], length {gU - gL}: "
          + ", ".join(f"{S}" + (f" x{g}" if g > 1 else "") for S, g, _, _ in lst))
