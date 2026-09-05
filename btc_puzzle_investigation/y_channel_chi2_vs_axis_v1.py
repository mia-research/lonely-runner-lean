#!/usr/bin/env python3
"""
y_channel_chi2_vs_axis_v1.py -- executes PREREG_y_channel_chi2_vs_axis_v1.md.
Decides: is the b=0-axis sub-Rayleigh deficit the chi2(y) 0.470 suppression (concentrated on the
order-2 multiplicative character), or a broader y-channel effect spread over the character spectrum?

Deficit spectrum D_V(k) = |V(k)| - E_r|V_rand(k)|, V(k)=sum_d chi_k(y_d) e_n(d), a0=1.
chi2 index k2=(p-1)/2. Concentration: chi2 share S, chi2 rank rho, top characters.
Calibration C1: chi2(y) saturation max_a|V_chi2(a)|/(4 sqrt p) ~ 0.47.  Null C2: random -> flat.
FLOAT only in character sums/FFT; verdict from ranks/shares replicated over 7 primes. No secp claim.
"""
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords

R = 200
SEED = 20260721
PRIMES = [163, 211, 349, 433, 577, 991, 2089]

def primroot(p):
    from sympy import primitive_root
    return int(primitive_root(p))

def dlog_table(p, g):
    ind = np.zeros(p, dtype=np.int64); v = 1
    for j in range(p - 1):
        ind[v] = j; v = v * g % p
    return ind                                   # ind[value]=j (value in 1..p-1)

def legendre(v, p):
    r = pow(int(v) % p, (p - 1) // 2, p)
    return -1 if r == p - 1 else r               # 0 only if v==0 (won't happen here)

def run(p, n, G, rng):
    xs, ys = group_coords(G, p, n, 0)
    yv = np.array(ys[1:], dtype=np.int64) % p
    d = np.arange(1, n)
    ec = np.exp(2j * np.pi * d / n)
    g = primroot(p); ind = dlog_table(p, g)
    jy = ind[yv]                                  # multiplicative index of each y_d
    k2 = (p - 1) // 2

    # V(k) for the character weighting e_n(d)
    M = np.zeros(p - 1, dtype=complex); np.add.at(M, jy, ec)
    V = np.abs(np.fft.fft(M))
    # random ensemble
    accV = np.zeros(p - 1)
    for _ in range(R):
        Mr = np.zeros(p - 1, dtype=complex)
        np.add.at(Mr, jy, np.exp(2j * np.pi * rng.random(n - 1)))
        accV += np.abs(np.fft.fft(Mr))
    ErV = accV / R
    DV = V - ErV
    aDV = np.abs(DV.copy()); aDV[0] = 0.0         # exclude trivial character

    S = abs(DV[k2]) / aDV.sum()
    rho = int(1 + np.sum(aDV > abs(DV[k2])))
    top = np.argsort(-aDV)[:6]
    is_chi2 = lambda k: "<-chi2" if k == k2 else ""

    # C1 calibration: chi2(y) saturation over a
    leg = np.array([legendre(v, p) for v in yv], dtype=float)
    sat = np.abs(np.fft.fft(leg)).max() / (4 * np.sqrt(p))

    # C2 null: a single random target's deficit spectrum flatness
    Mr = np.zeros(p - 1, dtype=complex); np.add.at(Mr, jy, np.exp(2j * np.pi * rng.random(n - 1)))
    DVr = np.abs(np.fft.fft(Mr)) - ErV; aDVr = np.abs(DVr.copy()); aDVr[0] = 0.0
    Sr = aDVr.max() / aDVr.sum()

    # l2 pinned check (forced)
    l2_char = (V ** 2).sum(); l2_rand = (ErV ** 2).sum()

    print(f"\n=== p={p} n={n}  k2(chi2)={k2}  primroot={g} ===", flush=True)
    print(f"  C1 chi2(y) saturation max_a|V_chi2(a)|/(4sqrt p) = {sat:.3f}  (M3: 0.470, band .432-.500)", flush=True)
    print(f"  chi2 deficit D_V(chi2) = {DV[k2]:+.4f}   (V_chi2={V[k2]:.3f} vs rand {ErV[k2]:.3f})", flush=True)
    print(f"  chi2 SHARE S = {S:.4f}  (uniform baseline 1/(p-2) = {1/(p-2):.4f})   chi2 RANK rho = {rho}", flush=True)
    print(f"  top-6 |D_V(k)|: " + "  ".join(f"k={int(k)}:{DV[int(k)]:+.3f}{is_chi2(int(k))}" for k in top), flush=True)
    print(f"  C2 null (random) max share Sr={Sr:.4f}  (should be ~uniform, small)", flush=True)
    print(f"  [forced] l2 char={l2_char:.1f} rand={l2_rand:.1f}  rel diff={abs(l2_char-l2_rand)/l2_rand:.2e}", flush=True)
    return dict(p=p, sat=sat, DVchi2=DV[k2], S=S, rho=rho, uniform=1/(p-2))

def main():
    rng = np.random.default_rng(SEED)
    res = []
    for p0 in PRIMES:
        r = prime_order_curve(p0, p0 + 40)
        if r: res.append(run(*r, rng))
    print("\n=== DETERMINATION (replicated over primes) ===", flush=True)
    print("  chi2 rank rho per prime:", [r["rho"] for r in res], flush=True)
    print("  chi2 share S vs uniform:", [f"{r['S']:.3f}/{r['uniform']:.4f}" for r in res], flush=True)
    print("  chi2 deficit sign (neg=suppressed):", [f"{r['DVchi2']:+.2f}" for r in res], flush=True)
    dom = sum(r["rho"] <= 3 for r in res)
    spread = sum(r["S"] < 5 * r["uniform"] for r in res)
    print(f"\n  chi2 dominant (rho<=3) at {dom}/{len(res)} primes;  chi2 share near-uniform (S<5x) at {spread}/{len(res)}", flush=True)
    print("  READ: dominant+high-share => SAME OBJECT (0.470 relocated);  near-uniform => DISTINCT broader y-suppression.", flush=True)

if __name__ == "__main__":
    main()
