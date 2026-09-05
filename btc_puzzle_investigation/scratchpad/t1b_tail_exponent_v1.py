#!/usr/bin/env python3
"""
t1b_tail_exponent_v1.py  —  T1b.0 (gate-free, CHARACTERIZATION not a verdict).

The −13.99σ sub-Rayleigh deficit's null is currently Rayleigh: P(|U|<eps) ~ eps^2 (complex Gaussian).
The interference frame flags this as probably WRONG for a real/low-dim trace distribution (~eps^1).
Which is it? Fit the small-value CDF exponent k in P(|U|/sqrt(n) < eps) ~ eps^k, pooled over a!=0 and
(b,c), for the real curve character sum U(a,b,c)=Σ_d e_p(b x_d + c y_d) e_n(a d), and compare to a
random-unit-phase target (the Rayleigh reference). k≈2 => Rayleigh holds; k≈1 => sub-Rayleigh real trace.

This is a distributional-SHAPE characterization; float |U| is analytic-size with integer args in the
sum (no key in the arg path). No verdict, no matched-null, no grade — a characterization per anomaly-drill.
"""
import math
import numpy as np
from eps_to_d_run_v1 import prime_order_curve, full_orbit


def coords(p, m, G):
    xs = full_orbit(G, p, m)
    ys = [None] * m
    # recover y for each multiple via the curve (exact): y^2 = x^3+7; use incremental point add
    from eps_to_d_run_v1 import padd, tonelli
    acc = None
    for d in range(1, m):
        acc = padd(acc, G, p)
        ys[d] = acc[1]
    return xs, ys


def U_row(xs, ys, b, c, p, n):
    idx = [d for d in range(1, n) if xs[d] is not None]
    ph = np.zeros(n, dtype=complex)
    arg = np.array([(b * xs[d] + c * ys[d]) % p for d in idx], dtype=float)
    ph[idx] = np.exp(2j * np.pi * arg / p)
    return np.fft.fft(ph)


def tail_exponent(mags, eps_grid):
    """fit k in P(m<eps) ~ eps^k by log-log slope over the small-value grid."""
    mags = np.sort(mags)
    N = len(mags)
    xs, ys = [], []
    for e in eps_grid:
        frac = np.searchsorted(mags, e) / N
        if frac > 0:
            xs.append(math.log(e)); ys.append(math.log(frac))
    if len(xs) < 2:
        return float('nan')
    xs = np.array(xs); ys = np.array(ys)
    return float(np.polyfit(xs, ys, 1)[0])   # slope = exponent k


def main():
    rng = np.random.default_rng(0)
    eps_grid = [0.05, 0.08, 0.12, 0.18, 0.25, 0.35]
    print("T1b.0 tail exponent k in P(|U|/sqrt(n) < eps) ~ eps^k  (Rayleigh k=2; sub-Rayleigh real k=1)\n")
    print(f"  {'p':>5} {'n':>5} {'k_real':>8} {'k_random':>9}  (b,c) pooled diag c=±b + axes")
    for (lo, hi) in [(547, 548), (1303, 1304), (2089, 2090)]:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, n, G = r
        xs, ys = coords(p, n, G)
        real_m, rand_m = [], []
        # pool over a diverse (b,c): c=0 axis, b=0 axis, c=+-b diagonal, a few generic
        bcs = [(1, 0), (2, 0), (0, 1), (1, 1), (1, -1 % p), (2, 2), (3, 3), (1, 7)]
        for (b, c) in bcs:
            U = U_row(xs, ys, b, c, p, n)
            mag = np.abs(U[1:]) / math.sqrt(n)         # a != 0
            real_m.extend(mag.tolist())
            # random-unit-phase target with same n (Rayleigh reference)
            ph = np.exp(2j * np.pi * rng.random(n))
            R = np.fft.fft(ph)
            rand_m.extend((np.abs(R[1:]) / math.sqrt(n)).tolist())
        k_real = tail_exponent(np.array(real_m), eps_grid)
        k_rand = tail_exponent(np.array(rand_m), eps_grid)
        print(f"  {p:>5} {n:>5} {k_real:>8.3f} {k_rand:>9.3f}")
    print("\n  Reading: k_random should be ~2 (Rayleigh calibration). If k_real is also ~2, the")
    print("  Rayleigh null is correct for the SHAPE; if k_real ~1, the deficit's null is mis-specified")
    print("  and T1b.1 (correct-null re-test) is mandatory. Characterization only; no verdict.")


if __name__ == "__main__":
    main()
