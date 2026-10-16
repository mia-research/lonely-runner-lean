#!/usr/bin/env python3
"""Integer sets at the small-alpha continuous failures of the pair-window fold (s5_pf_v4: k = 2, alpha ~ 0.12-0.24,
lam = (v4 - v2)/v1 ~ 1.15-1.5, mu ~ 1/3): v1 = 2D, v2 ~ v1/alpha, v3 = v2 + D, v4 ~ v2 + lam v1, v5 in {v4+1, v4+2}.
For each: non-uniform at j0?, simple pair fold?, and the closing witness (first four-block fold, or sharp window_two)."""
import math
from fractions import Fraction as F
from collections import Counter
exec(open("s5_exc_v1.py").read().split("\nH = int(")[0])
c = Counter(); shown = 0
for D in (5, 7, 10, 13):
    for al in (0.12, 0.13, 0.14, 0.22, 0.24):
        v1 = 2 * D; v2 = round(v1 / al); v3 = v2 + D
        for lam in (1.15, 1.25, 1.35, 1.45):
            v4 = v2 + round(lam * v1)
            if v4 <= v3: continue
            for v5 in (v4 + 1, v4 + 2):
                S = (v1, v2, v3, v4, v5)
                if not s5(S) or uni_j0(S): c["uniform or not §5"] += 1; continue
                if simple_fold(S): c["simple fold closes"] += 1; continue
                w = witness(S); c["exception: " + w.split(", start")[0].split(" at pair")[0]] += 1
                if shown < 12: print(S, "k=2 alpha/amax=%.2f lam=%.2f" % (F(v1, v2) / F(2, 5), F(v4 - v2, v1)), diag(S)[4], w); shown += 1
print(dict(c))
