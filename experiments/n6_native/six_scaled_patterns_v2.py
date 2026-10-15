#!/usr/bin/env python3
"""As v1, all k <= KMAX and every e up to the window bound (e <= 40k for (1,3,4,5), e <= 23k for (1,2,3,5));
beyond the bound an opening must meet a component of L(kP) (window longer than 1/e). Integer residue test
replaces Fractions: k t_j in L(P) is checked exactly via the residue criterion of kP at flank e."""
import sys, math
KMAX = int(sys.argv[1])
def fails(P, k, e):
    S = [k * p for p in P]
    for j in range(e):
        m = 6 * j + 1
        if all(e <= (d * m) % (6 * e) <= 5 * e for d in S): return False
    return True
for P, bound in [((1, 3, 4, 5), 40), ((1, 2, 3, 5), 23)]:
    out = []
    for k in range(1, KMAX + 1):
        for e in range(5 * k + 1, bound * k + 1):
            if math.gcd(math.gcd(*[k * p for p in P]), e) != 1 or e in [k * p for p in P]: continue
            if fails(P, k, e): out.append((k, e))
    print(f"P={P}: failing (k, e) for k <= {KMAX}, e <= {bound}k: {out}")
