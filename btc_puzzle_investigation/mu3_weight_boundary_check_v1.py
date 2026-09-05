#!/usr/bin/env python3
"""Boundary of the forced-zero rule: which statistics over a beta-closed multiset
are forced to 0 and which are NOT.  Exact arithmetic; small prime instrument."""
import random
from collections import Counter

p0 = 103                      # p0 % 9 == 4 -> (p0-1)//3 = 34; check chi3(beta) primitive
cb = (p0 - 1) // 3
g = 2
while pow(g, cb, p0) == 1:
    g += 1
beta = pow(g, cb, p0)
assert pow(beta, 3, p0) == 1 and beta != 1

ZERO, ONE, W, W2 = (0, 0), (1, 0), (0, 1), (-1, -1)
OM = (ONE, W, W2)
pw = {1: 0, beta: 1, beta * beta % p0: 2}
def t3(v): return pw[pow(v % p0, cb, p0)]
def zadd(u, v): return (u[0] + v[0], u[1] + v[1])

# a beta-closed multiset V (orbits of size 3, x != 0)
rng = random.Random(7)
V = Counter()
for _ in range(11):
    x = rng.randrange(1, p0)
    for e in range(3):
        V[x * pow(beta, e, p0) % p0] += 1
assert Counter({beta * k % p0: v for k, v in V.items()}) == V, "V not beta-closed"
n = sum(V.values())

# (1) WEIGHT-1 multiplicative character: forced to exactly 0
M3 = ZERO
cls = [0, 0, 0]
for v, m in V.items():
    for _ in range(m):
        M3 = zadd(M3, OM[t3(v)]); cls[t3(v)] += 1
print(f"beta={beta} |V|={n} support={len(V)}")
print(f"(1) weight-1 chi3 sum over beta-closed V : M3={M3}  classes={cls}   -> FORCED ZERO: {M3==ZERO}")

# (2) WEIGHT-0 statistic (a COUNT): not forced
print(f"(2) weight-0 count |V|                   : {n}                     -> forced zero: {n==0}")

# (3) WEIGHT-0 multiplicative character (chi2, beta is a cube hence a QR here): not forced
def chi2(v): return 1 if pow(v % p0, (p0 - 1) // 2, p0) == 1 else -1
print(f"    chi2(beta)={chi2(beta)} (weight 0 iff +1)")
S2 = sum(chi2(v) * m for v, m in V.items())
print(f"(3) weight-0 chi2 sum over beta-closed V : {S2}                    -> forced zero: {S2==0}")

# (4) ADDITIVE character: NOT forced at fixed b; instead Fhat(b) == Fhat(beta*b)
def Fhat(b):
    # exact: represent sum_v zeta_p^{b v} by its exponent histogram
    h = [0] * p0
    for v, m in V.items():
        h[b * v % p0] += m
    return tuple(h)
bs = [b for b in range(1, p0)]
sym = sum(1 for b in bs if Fhat(b) == Fhat(beta * b % p0))
# a genuine vanishing would need the histogram to be constant across all residues
van = sum(1 for b in bs if len(set(Fhat(b))) == 1)
print(f"(4) additive: Fhat(b)==Fhat(beta*b) for  : {sym}/{len(bs)} b   (a symmetry IN b)")
print(f"    additive: exact vanishings Fhat(b)=0 : {van}/{len(bs)} b   -> NOT forced")
