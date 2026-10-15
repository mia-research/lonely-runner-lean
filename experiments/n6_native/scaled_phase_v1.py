#!/usr/bin/env python3
"""Phase classes for scaled blocking patterns at order n. For gcd(k, e) = 1 the scaled openings k t_j mod 1,
t_j = (j + 1/n)/e, are the grid (i + r/n)/e with r = k mod n, so whether kP + {e} fails at its largest flank
depends on (r, e) only. For each r and e (gcd(k,e) = 1 assumed via a representative k = r or r + n coprime to e),
records whether the grid misses L_n(P) (exact residue test with representative k). Then for each actual k,
the failing e are those of its class with e > max(kP) = (max P) k.
Usage: scaled_phase_v1.py n EMAX p1 p2 ...  (P a coarse blocking pattern at order n)"""
import sys, math
n, EMAX = int(sys.argv[1]), int(sys.argv[2]); P = [int(x) for x in sys.argv[3:]]
def fails(k, e):
    S = [k * p for p in P]
    return not any(all(e <= (d * (n * j + 1)) % (n * e) <= (n - 1) * e for d in S) for j in range(e))
cls = {}
for r in range(n):
    out = []
    for e in range(2, EMAX + 1):
        k = next((kk for kk in range(r if r else n, r + 50 * n, n) if math.gcd(kk, e) == 1), None)
        if k is None: continue
        if fails(k, e): out.append(e)
    cls[r] = out
    print(f"n={n} P={P} phase class r = k mod n = {r}: grid misses L for e in {out}")
mx = max(P)
print("actual k (e > max(kP) = %d k, gcd(k,e)=1, gcd(kP,e)=1) with failing e:" % mx)
for k in range(1, 4 * n + 1):
    es = [e for e in cls[k % n] if e > mx * k and math.gcd(k, e) == 1]
    if es: print(f"   k={k} (r={k % n}): {es}")
