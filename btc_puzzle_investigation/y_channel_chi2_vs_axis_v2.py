#!/usr/bin/env python3
"""
y_channel_chi2_vs_axis_v2.py -- v2 of the chi2(y)-vs-axis determination, with the fixes from the
v1 control failure (see PREREG_..._DEVIATIONS): (a) calibration is now the FORCED Sy fact
Re V(chi2)=0 at p=3 mod4 (a clean channel check), NOT the max-over-a 0.470 (a different statistic
from the a0=1 axis); (b) split by residue class p=1 vs p=3 mod4 to isolate the forced suppression;
(c) dropped the wrong 'l2 pinned' check (l2 is NOT pinned in the multiplicative-char basis).

Determination: is the b=0 axis a0=1 mean-magnitude deficit carried by the chi2 character
specifically (=> the 0.470 relocated), or spread over the y multiplicative-character spectrum
(=> a distinct broad distributional effect)?  Decided in the CLEAN p=1 mod4 class.
FLOAT only in character sums/FFT. Model primes only, a0=1. No secp/extraction claim.
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
    return ind

def run(p, n, G, rng):
    xs, ys = group_coords(G, p, n, 0)
    yv = np.array(ys[1:], dtype=np.int64) % p
    d = np.arange(1, n)
    ec = np.exp(2j * np.pi * d / n)
    g = primroot(p); ind = dlog_table(p, g); jy = ind[yv]
    k2 = (p - 1) // 2

    # multiplicative-character readouts V(k) at a0=1, and the deficit spectrum
    M = np.zeros(p - 1, dtype=complex); np.add.at(M, jy, ec)
    Vc = np.fft.fft(M)                                  # complex V(k)
    V = np.abs(Vc)
    accV = np.zeros(p - 1)
    for _ in range(R):
        Mr = np.zeros(p - 1, dtype=complex); np.add.at(Mr, jy, np.exp(2j * np.pi * rng.random(n - 1)))
        accV += np.abs(np.fft.fft(Mr))
    DV = V - accV / R
    aDV = np.abs(DV.copy()); aDV[0] = 0.0
    rho = int(1 + np.sum(aDV > abs(DV[k2])))
    S = abs(DV[k2]) / aDV.sum()

    # axis mean-magnitude deficit (the located finding), recomputed for consistency
    #  A(c)=U(1,0,c): histogram e_n(d) over y, FFT over y (length p)
    Hy = np.zeros(p, dtype=complex); np.add.at(Hy, yv, ec)
    A = np.abs(np.fft.fft(Hy))                          # |A(c)|, c=0..p-1
    accA = np.zeros(p)
    for _ in range(R):
        Hr = np.zeros(p, dtype=complex); np.add.at(Hr, yv, np.exp(2j * np.pi * rng.random(n - 1)))
        accA += np.abs(np.fft.fft(Hr))
    ErA = accA / R
    axis = np.arange(p) != 0
    axis_def = 100 * (A[axis].mean() - ErA[axis].mean()) / ErA[axis].mean()

    # CALIBRATION C1 (forced): Re V(chi2)=0 at p=3 mod4  (channel check, exact)
    reV, imV = Vc[k2].real, Vc[k2].imag
    p3 = (p % 4 == 3)
    chan_ok = (abs(reV) < 1e-6) if p3 else True

    print(f"  p={p:5d} (p%4={p%4}) n={n:5d}  axis_def={axis_def:+.2f}%  "
          f"D_V(chi2)={DV[k2]:+.2f}  chi2_rank={rho:4d}  chi2_share={S:.4f}(unif {1/(p-2):.4f})  "
          f"V(chi2)={V[k2]:.2f} [Re={reV:+.3f} Im={imV:+.3f}]  chanC1={'OK' if chan_ok else 'FAIL'}", flush=True)
    return dict(p=p, p3=p3, axis_def=axis_def, DVchi2=DV[k2], rho=rho, S=S, chan_ok=chan_ok)

def main():
    rng = np.random.default_rng(SEED)
    print("=== per prime (a0=1): axis deficit vs chi2 mode ===", flush=True)
    res = [run(*prime_order_curve(p0, p0 + 40), rng) for p0 in PRIMES]

    print("\n=== CALIBRATION C1 (channel check) ===", flush=True)
    p3s = [r for r in res if r["p3"]]
    print(f"  Re V(chi2)~0 at p=3mod4: {all(r['chan_ok'] for r in p3s)}  "
          f"(primes {[r['p'] for r in p3s]})  -- confirms chi2(y) channel is correctly computed", flush=True)

    print("\n=== DETERMINATION, split by residue class ===", flush=True)
    for lab, cls in (("p=1 mod4 (CLEAN, no Sy forcing)", [r for r in res if not r["p3"]]),
                     ("p=3 mod4 (Sy-forced, confound)", p3s)):
        print(f"  {lab}:", flush=True)
        print(f"     axis_def%    : {[round(r['axis_def'],2) for r in cls]}", flush=True)
        print(f"     D_V(chi2)    : {[round(r['DVchi2'],2) for r in cls]}   (sign consistency = chi2 carries it?)", flush=True)
        print(f"     chi2 rank    : {[r['rho'] for r in cls]}   (1=dominant; high=chi2 not special)", flush=True)
    clean = [r for r in res if not r["p3"]]
    axis_robust = all(r["axis_def"] < 0 for r in res)
    chi2_dom = sum(r["rho"] <= 3 for r in clean)
    chi2_signconsistent = len(set(np.sign([r["DVchi2"] for r in clean]))) == 1
    print("\n  READ:", flush=True)
    print(f"   axis deficit negative at ALL 7 primes: {axis_robust}", flush=True)
    print(f"   in CLEAN class: chi2 dominant (rank<=3) at {chi2_dom}/{len(clean)}; chi2 deficit sign-consistent: {chi2_signconsistent}", flush=True)
    print("   => axis deficit is chi2-specific (0.470 relocated) ONLY IF chi2 dominant & sign-consistent in the clean class.", flush=True)

if __name__ == "__main__":
    main()
