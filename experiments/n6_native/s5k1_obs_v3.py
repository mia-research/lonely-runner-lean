#!/usr/bin/env python3
"""§5 k = 1, primitive <= H. (a) the set(s) with no closing window for t <= 3/v1, and the first lonely instant of each by a
longer scan; (b) for sets with a 123-triangle closing window: the earliest one -- runner 1's lap m1, triangle (s/a),
x1 and {x2} at the window start, closer (W, F5, F4) -- and the distribution by ratio a = v2/v1; (c) F3-only sets: their
ratios (a, v4/v1, v5/v1) and the earliest F3 window (laps)."""
import math, sys
from itertools import combinations
from collections import Counter, defaultdict
from s5k1_obs_v2 import bands, inter, block, sharp, k1, types, EPS
def earliest123(S):
    v1, v2, v3, v4, v5 = S; T = 3 / v1; best = None
    b123 = block([v1, v2, v3], T)
    for L, U, ms in b123:
        tri = "s" if ms[2] == ms[0] + ms[1] else "a"
        if sharp(U - L, v4, v5): c = (L, "W", tri, ms); best = min(best, c) if best else c
        for (x, y, nm) in ((v4, v5, "F5"), (v5, v4, "F4")):
            for L2, U2, m2 in inter([(L, U, ms)], bands(x, T)):
                if y * (U2 - L2) >= 1 / 3 - EPS:
                    c = (L2, nm, tri, ms); best = min(best, c) if best else c
    return best
H = int(sys.argv[1]) if len(sys.argv) > 1 else 50
sets = [S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and k1(S)]
none = []; dist = Counter(); bya = defaultdict(Counter); f3only = []
for S in sets:
    ts = types(S)
    if not ts: none.append(S); continue
    e = earliest123(S)
    if e:
        L, cl, tri, ms = e; v1, v2 = S[0], S[1]
        x1 = L * v1; x2 = (L * v2) % 1
        dist[(ms[0], tri, cl)] += 1
        a = v2 / v1; bya["a<4" if a < 4 else ("4<=a<10" if a < 10 else "a>=10")][(ms[0], tri)] += 1
    elif "F3" in ts: f3only.append(S)
print("no closing window for t <= 3/v1:", none)
for S in none:
    for T in (6, 12, 24):
        b = block(list(S), T / S[0])
        if b: print("  ", S, f"first box window within t <= {T}/v1:", [(round(L * S[0], 4), round(U * S[0], 4), ms) for L, U, ms in b[:2]]); break
print("earliest 123-window (m1, triangle, closer):", dist.most_common(12))
for k, v in bya.items(): print("  ", k, v.most_common(6))
print("F3-only:", len(f3only), [(S, round(S[1] / S[0], 2), round(S[3] / S[0], 2), round(S[4] / S[0], 2)) for S in f3only[:12]])
