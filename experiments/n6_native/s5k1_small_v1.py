#!/usr/bin/env python3
"""§5 k = 1, the small-alpha limit. Runner 1 reads p (slow); within one lap of runner 2 runners 2, 3, 4 read y, y + p, y + lam p
(lam = (v4 - v2)/v1 > 1). Their common clear set in y has length 2/3 - spread({0, p, lam p} mod 1) (circular spread).
Runner 5 is folded on it when that length >= mu' = v2/(3 v5) < 1/3. For lam on a grid in (1, 40]: the smallest spread over
p in [1/6, 5/6 - margin], the set of p achieving spread <= 1/3 - gap (gap = 0, 0.02), and the lam where none exists."""
def spread(pts):
    s = sorted(x % 1 for x in pts)
    gaps = [s[i + 1] - s[i] for i in range(len(s) - 1)] + [1 - s[-1] + s[0]]
    return 1 - max(gaps)
bad = []; rows = []
N = 4000
for li in range(1, 3901):
    lam = 1 + li / 100
    best = min((spread([0, p, lam * p]), p) for p in (1 / 6 + (2 / 3 - 0.03) * i / N for i in range(N + 1)))
    rows.append((lam, best))
    if best[0] > 1 / 3 - 0.02: bad.append((round(lam, 2), round(best[0], 4), round(best[1], 4)))
print("lam with min spread > 1/3 - 0.02 (no p leaves a clear arc of 1/3 + 0.02 for runners 2, 3, 4):")
import itertools
groups = []
for l in bad:
    if groups and abs(l[0] - groups[-1][-1][0]) < 0.011: groups[-1].append(l)
    else: groups.append([l])
for g in groups: print("   lam in [%.2f, %.2f], worst min spread %.4f" % (g[0][0], g[-1][0], max(x[1] for x in g)))
print("max over lam of min spread:", max(r[1][0] for r in rows))
