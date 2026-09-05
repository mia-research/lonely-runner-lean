#!/usr/bin/env python3
"""chi2(y) harmonic analysis + multi-point joint. Exact big-int in the signal path;
float only for the Fourier phase (ranked against the 1/sqrt(M) floor)."""
import numpy as np, random, cmath, math
import sys
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from ecc_secp256k1 import P as p, N_ORDER as n, scalar_mul

def affine_add(P1, P2):
    if P1 is None: return P2
    if P2 is None: return P1
    (x1, y1), (x2, y2) = P1, P2
    if x1 == x2 and (y1 + y2) % p == 0: return None
    if P1 == P2:
        s = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
    else:
        s = (y2 - y1) * pow((x2 - x1) % p, -1, p) % p
    x3 = (s * s - x1 - x2) % p; y3 = (s * (x1 - x3) - y1) % p
    return (x3, y3)

def chi2(v): return 1 if pow(int(v), (p - 1) // 2, p) == 1 else -1

# ---- sample points ----
M = 40000
rng = random.Random(7)
D = [rng.randrange(1, n) for _ in range(M)]
PTS = [scalar_mul(d) for d in D]
F = np.array([chi2(P[1]) for P in PTS], dtype=np.float64)   # f(d) = chi2(y) in {+-1}
Dobj = np.array(D, dtype=object)
print(f"M={M}  mean f = {F.mean():+.4f}  (floor 1/sqrt(M) = {1/math.sqrt(M):.4f})")

# ---- additive Fourier: c_k = (1/M) sum f_j exp(-2pi i (k d_j mod n)/n) ----
K = 200
mags = []
for k in range(1, K + 1):
    r = (k * Dobj) % n                      # exact big-int mod
    ang = np.array([2 * math.pi * (int(v) / n) for v in r])  # phase in [0,2pi)
    c = np.mean(F * np.exp(-1j * ang))
    mags.append(abs(c))
mags = np.array(mags)
top = np.argsort(mags)[::-1][:6]
print("\nADDITIVE Fourier |c_k|, k=1..%d:" % K)
print(f"  max |c_k| = {mags.max():.4f} at k={top[0]+1}   floor~{1/math.sqrt(M):.4f}")
print("  top-6 (k, |c_k|):", [(int(t+1), round(float(mags[t]), 4)) for t in top])
print(f"  # of k with |c_k| > 3/sqrt(M): {(mags > 3/math.sqrt(M)).sum()} (expect ~few by chance)")

# ---- multiplicative characters of small order m | (n-1) ----
print("\nMULTIPLICATIVE characters c_psi = E[f(d) psi(d)] (psi order m):")
gg = 2
while pow(gg, (n - 1) // 2, n) == 1: gg += 1   # generator-ish
# use psi(d) = exp(2pi i * a * ind(d)/(n-1)); we can't take discrete logs, so instead
# test psi(d)=chi_m(d)=d^((n-1)/m) mapped to m-th roots of unity, for small m.
for m in (2, 3, 4, 6, 12):
    if (n - 1) % m: continue
    e = (n - 1) // m
    # psi(d) = zeta_m^{ind}, computed as the m-th root pow(d,e,n) sits at
    vals = np.array([pow(d, e, n) for d in D], dtype=object)
    # map each m-th root of unity value to its exponent j (0..m-1)
    z = pow(gg, e, n)
    table = {pow(z, j, n): j for j in range(m)}
    jj = np.array([table.get(int(v), -1) for v in vals])
    if (jj < 0).any():
        print(f"  order {m}: (root table miss, skip)"); continue
    psi = np.exp(2j * math.pi * jj / m)
    c = np.mean(F * psi)
    print(f"  order {m:2d}: |c_psi| = {abs(c):.4f}   (floor {1/math.sqrt(M):.4f})")

# ---- MULTI-POINT joint: (f(d), f(d+k)) for small k ----
print("\nMULTI-POINT joint I(f(d); f(d+k)) via 2x2 (deviation from independence):")
def mi_pm(a, b):
    N = len(a); mi = 0.0
    for u in (-1, 1):
        for v in (-1, 1):
            pj = np.mean((a == u) & (b == v)); pu = np.mean(a == u); pv = np.mean(b == v)
            if pj > 0: mi += pj * math.log2(pj / (pu * pv))
    return mi
Mk = 15000
rng2 = random.Random(11)
Dk = [rng2.randrange(1, n) for _ in range(Mk)]
Pd = [scalar_mul(d) for d in Dk]
fd = np.array([chi2(P[1]) for P in Pd])
for k in (1, 2, 3, 7):
    kG = scalar_mul(k)
    fdk = np.array([chi2(affine_add(P, kG)[1]) for P in Pd])
    raw = mi_pm(fd, fdk)
    nulls = [mi_pm(fd, fdk[np.random.permutation(Mk)]) for _ in range(200)]
    mu, sd = np.mean(nulls), np.std(nulls) + 1e-12
    print(f"  k={k}: I={raw:.5f} bits, z={(raw-mu)/sd:+.1f}  corr(f_d,f_dk)={np.mean(fd*fdk):+.4f}")
