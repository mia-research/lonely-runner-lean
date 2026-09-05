#!/usr/bin/env python3
"""
Decisive test of the order-64 standout: does chi2(y([d]G)) depend on
b(d) = ind_64(d) = d^((n-1)/64) mapped to Z/64  (an EFFICIENTLY computable function
of d, no DLP)?  If yes -> a real computable relation between the y-hardcore-bit and a
2-adic multiplicative coordinate of d. If flat -> the |c_64|~0.013 was small-sample noise.

Forced symmetry sanity check: oddness f(-d)=-f(d) with b(-d)=b(d)+32 => bucket means
must satisfy E[f|b=j+32] = -E[f|b=j] (even frequencies zero). The question is whether
the ODD frequencies (order-64 char = freq 1) carry a coherent nonzero component.
"""
import numpy as np, random, math
from ecc_secp256k1 import P as p, N_ORDER as n, scalar_mul
fac = [2, 3, 149, 631, 107361793816595537, 174723607534414371449,
       341948486974166000522343609283189]
g = next(gg for gg in range(2, 200) if all(pow(gg, (n - 1) // q, n) != 1 for q in fac))
e64 = (n - 1) // 64
z64 = pow(g, e64, n)
TAB = {pow(z64, j, n): j for j in range(64)}
def chi2(v): return 1.0 if pow(int(v), (p - 1) // 2, p) == 1 else -1.0

M = 80000
rng = random.Random(2024)
F = np.empty(M); B = np.empty(M, dtype=int)
for i in range(M):
    d = rng.randrange(1, n)
    F[i] = chi2(scalar_mul(d)[1])
    B[i] = TAB[pow(d, e64, n)]

# bucket means
means = np.array([F[B == j].mean() if (B == j).sum() else 0.0 for j in range(64)])
cnt = np.array([(B == j).sum() for j in range(64)])
# forced relation check
anti = np.mean([abs(means[j] + means[(j + 32) % 64]) for j in range(64)])
print(f"M={M}; per-bucket count ~{cnt.mean():.0f}; forced anti-symmetry mean|E[f|j]+E[f|j+32]| = {anti:.4f} (small=holds)")

# full DFT over Z/64: c_k = (1/64) sum_j means[j] but weighted by counts -> use full corr
# proper: c_k = (1/M) sum_i f_i exp(-2pi i k b_i /64)
ang = 2 * math.pi * B / 64
ck = np.array([abs(np.mean(F * np.exp(-1j * k * ang))) for k in range(64)])
floor = 1 / math.sqrt(M)
print(f"floor 1/sqrt(M) = {floor:.4f}  (noise mean |c_k| ~ {0.886*floor:.4f})")
order = np.argsort(ck[1:])[::-1][:6] + 1
print("top-6 frequencies k (of Z/64) by |c_k|:", [(int(k), round(float(ck[k]), 4)) for k in order])
print(f"  |c_1| (order-64 char) = {ck[1]:.4f};  even-freq max (should be ~0) = {ck[2::2].max():.4f}")

# permutation null on the whole Z/64 dependence: max_k |c_k| vs permuted
rr = np.random.default_rng(1)
null_max = np.array([max(abs(np.mean(F[rr.permutation(M)] * np.exp(-1j * k * ang)))
                         for k in range(1, 64)) for _ in range(200)])
obs_max = ck[1:].max()
z = (obs_max - null_max.mean()) / (null_max.std() + 1e-12)
print(f"\nDECISIVE: max_k|c_k| observed = {obs_max:.4f}; permutation-null max mean = "
      f"{null_max.mean():.4f} +/- {null_max.std():.4f};  z = {z:+.1f}")
print("  => z>~3 and concentrated at odd k = REAL computable structure; z~0 = noise.")

# power-scaling of c_1 specifically
print("\nc_1 vs M (does it hold or decay like 1/sqrt(M)?):")
for MM in (10000, 20000, 40000, 80000):
    print(f"  M={MM:5d}: |c_1|={abs(np.mean((F*np.exp(-1j*ang))[:MM])):.4f}  floor={1/math.sqrt(MM):.4f}")
