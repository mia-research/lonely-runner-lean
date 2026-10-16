#!/usr/bin/env python3
"""§5 k = 1, small alpha: the IVT box criterion. v2 = 1/alpha (v1 = 1), v3 = v2 + 1, v4 = v2 + lam, v5 = v2 + lam5
(lam5 = (v5 - v2)/v1). At any instant runners 2..5 read y, y + P, y + lam P, y + lam5 P (P = runner 1's reading). If on an
interval of P of length >= alpha (inside a runner-1 band) the points {0, P, lam P, lam5 P} keep circular spread <= 2/3 with the
same arc arrangement, an exact lonely instant exists (intermediate values: y - lower envelope rises by >= 1 per lap of
runner 2). Test: for alpha in a list and (lam, nu = v5/v4) on a grid (non-uniform region beta = lam alpha < 0.51), the
longest run of P (grid step alpha/8, P in [n+1/6, n+5/6], n < 3) with spread <= 2/3; report cases where it is < alpha."""
import math
def spread(pts):
    s = sorted(x % 1 for x in pts)
    gaps = [s[i + 1] - s[i] for i in range(len(s) - 1)] + [1 - s[-1] + s[0]]
    return 1 - max(gaps)
def longest(al, lam, lam5):
    step = al / 8; best = 0
    for n in range(3):
        run = 0; P = n + 1 / 6
        while P <= n + 5 / 6:
            if spread([0, P, lam * P, lam5 * P]) <= 2 / 3: run += step; best = max(best, run)
            else: run = 0
            P += step
        if best >= al: return best
    return best
bad = []; tot = 0
for al in (0.04, 0.02, 0.01, 0.003):
    for li in range(1, 61):
        lam = 1 + li * 0.1
        if lam * al >= 0.5: continue
        for nu in (1.0001, 1.001, 1.01, 1.03, 1.1, 1.3, 1.7, 2.5, 4):
            lam5 = ((1 + lam * al) * nu - 1) / al
            tot += 1
            b = longest(al, lam, lam5)
            if b < al: bad.append((al, round(lam, 2), nu, round(lam5, 2), round(b / al, 2)))
print(f"cases {tot}, failing the IVT box criterion: {len(bad)}")
for x in bad[:25]: print("  alpha, lam, nu, lam5, longest/alpha:", x)
