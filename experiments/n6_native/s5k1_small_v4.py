#!/usr/bin/env python3
"""§5 k = 1 small alpha, two leaf criteria with a fine P grid (step = min(alpha, 1/(lam5+1))/20):
 BOX (gamma = (v5 - v2)/v2 <= 1/2): a run of P of length >= alpha with spread{0, P, lam P, lam5 P} <= 2/3.
 FOLD (gamma > 1/2): a run of P of length >= alpha (1 + 1) where the clear arc of runners 2, 3, 4,
     2/3 - spread{0, P, lam P}, is >= 1/(3 (1 + gamma)) + (1 + lam) alpha  (window for runner 5's fold plus drift).
Grid: alpha in (0.04 ... 0.001), lam geometric up to the uniform cut (lam alpha < 0.51), gamma in a list.
Reports failures and the smallest margin ratio."""
import math
def spread(pts):
    s = sorted(x % 1 for x in pts)
    gaps = [s[i + 1] - s[i] for i in range(len(s) - 1)] + [1 - s[-1] + s[0]]
    return 1 - max(gaps)
def run_len(al, ok, step):
    best = 0
    for n in range(3):
        run = 0; P = n + 1 / 6
        while P <= n + 5 / 6:
            if ok(P): run += step; best = max(best, run)
            else: run = 0
            P += step
    return best
bad = []; tot = 0; worst = (9, None)
for al in (0.04, 0.025, 0.01, 0.004, 0.001):
    lam = 1.05
    while lam * al < 0.51:
        for g in (0.0, 0.001, 0.01, 0.05, 0.2, 0.5, 0.51, 0.8, 1.5, 4, 20):
            lam5 = max(lam + 1e-9, g / al)
            tot += 1
            if g <= 0.5:
                step = min(al, 1 / (lam5 + 1)) / 20
                b = run_len(al, lambda P: spread([0, P, lam * P, lam5 * P]) <= 2 / 3, step); need = al; kind = "BOX"
            else:
                step = min(al, 1 / (lam + 1)) / 20
                thr = 1 / (3 * (1 + g)) + (1 + lam) * al
                b = run_len(al, lambda P: 2 / 3 - spread([0, P, lam * P]) >= thr, step); need = 2 * al; kind = "FOLD"
            r = b / need
            if r < worst[0]: worst = (round(r, 3), kind, al, round(lam, 3), g)
            if b < need: bad.append((kind, al, round(lam, 3), g, round(r, 3)))
        lam *= 1.07
print(f"cases {tot}, failing: {len(bad)}; smallest run/need {worst}")
for x in bad[:30]: print("  ", x)
