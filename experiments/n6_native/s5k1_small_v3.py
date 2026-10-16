#!/usr/bin/env python3
"""As s5k1_small_v2, wider: lam up to the uniform cut (beta = lam alpha < 0.51, geometric grid), nu up to 50, alpha down to
0.001. Also reports the smallest longest/alpha ratio met, and where."""
import math
exec(open("s5k1_small_v2.py").read().split("bad = []; tot = 0")[0])
bad = []; tot = 0; worst = (9, None)
for al in (0.04, 0.025, 0.01, 0.004, 0.001):
    lam = 1.05
    while lam * al < 0.51:
        for nu in (1.00001, 1.0003, 1.003, 1.03, 1.2, 1.6, 2.5, 6, 20, 50):
            lam5 = ((1 + lam * al) * nu - 1) / al
            tot += 1
            b = longest(al, lam, lam5)
            r = b / al
            if r < worst[0]: worst = (r, (al, round(lam, 3), nu))
            if b < al: bad.append((al, round(lam, 3), nu, round(lam5, 2), round(r, 2)))
        lam *= 1.07
print(f"cases {tot}, failing: {len(bad)}; smallest longest/alpha {worst}")
for x in bad[:25]: print("  ", x)
