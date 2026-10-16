#!/usr/bin/env python3
"""Continuous map of the §5 pair-window fold, k >= 2. Parameters: k, alpha = v1/v2 = kD/v2 in (0, k/(3k-1)),
beta = (v4 - v2)/v2 > alpha/k, mu = v4/(3 v5) in (0, 1/3]. Derived: v3/v2 = 1 + alpha/k, rho = v1/v3 = alpha/(1+alpha/k),
q = v4/v3 = (1+beta)/(1+alpha/k), gamma = (v5 - v2)/v2 = (1+beta)/(3 mu) - 1.
At lap j: u = j + 1/6, p = alpha u, h = 2/3 - p/k >= 0, runner 1 on lap n1 needs p - n1 in [1/6, 5/6 - rho h];
 fold5: w = q h >= mu and beta u in [m - w + mu, m + 2/3 - mu];
 fold4: runner 5 in the block: w5 = (v5/v3) h >= v5/(3 v4) = 1/(9 mu) * ... i.e. stretch of runner 5 >= v5/(3 v4), with
        runner 5's offset gamma u: gamma u in [m - w5 + mu5, m + 2/3 - mu5], mu5 = v5/(3 v4) = 1/(9 mu)... (mu5 <= 1/3 needs mu >= 1/3 -> only mu = 1/3)
Uniform at j0 (j0 = ceil(1/(6 alpha) - 1/6)): 3 v4 h0 >= 2 v3, i.e. 3 q h0 >= 2 (then window_two closes): excluded.
Report the share of (alpha, beta, mu) grid points (per k) not closed by fold5 over all j, inside the non-uniform domain,
and the alpha range of the failures."""
import math
from fractions import Fraction as F
from collections import Counter
def closes(k, al, be, mu):
    rho = al / (1 + al / k); q = (1 + be) / (1 + al / k)
    j = 0
    while True:
        u = j + 1 / 6; p = al * u; h = 2 / 3 - p / k
        if h < 0: return False
        n1 = math.floor(p - 1 / 6)
        if p - n1 + rho * h <= 5 / 6:
            w = q * h
            if w >= mu:
                z = be * u; m = math.ceil(z - 2 / 3 + mu)
                if m - w + mu <= z: return True
        j += 1
def nonuniform(k, al, be):
    q = (1 + be) / (1 + al / k); j0 = max(0, math.ceil(1 / (6 * al) - 1 / 6)); p0 = al * (j0 + 1 / 6)
    h0 = 2 / 3 - p0 / k
    return 3 * q * h0 < 2
for k in (2, 3, 4, 6, 10, 100):
    amax = k / (3 * k - 1); tot = bad = 0; ar = Counter()
    for ai in range(1, 60):
        al = amax * ai / 60
        for bi in range(1, 80):
            be = al / k + 1.2 * bi / 80
            if not nonuniform(k, al, be): continue
            for mi in range(1, 21):
                mu = mi / 60; tot += 1
                if not closes(k, al, be, mu): bad += 1; ar[round(al / amax, 1)] += 1
    print(f"k = {k}: non-uniform grid points {tot}, fold5 fails at {bad} ({bad / max(tot,1):.3f}); failures by alpha/alpha_max: {sorted(ar.items())}")
