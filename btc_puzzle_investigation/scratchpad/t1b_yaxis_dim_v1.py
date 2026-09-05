#!/usr/bin/env python3
"""
t1b_yaxis_dim_v1.py — gate-free: is the y-only sum U(a,0,c) collapsed onto a 1-D line (k≈1 = forced
geometry, dead end) or is there a 2-D RESIDUAL after projecting the dominant axis out (a place a
signal could hide)? Follows RESULT_t1b_tail_geometry (y-axis k≈1 vs x-axis k≈2).

For each (b,c): scatter {(Re U(a), Im U(a)) : a!=0}; principal variances λ1>=λ2 (2x2 covariance).
  λ2/λ1 ≈ 0  => 1-D line (forced); residual (minor axis) is the off-line component.
  λ2/λ1 ≈ 1  => 2-D isotropic (Rayleigh).
Then fit the tail exponent of the RESIDUAL (minor-axis) magnitude: if it goes Rayleigh(2), the y-axis
is fully forced; if it stays sub-Rayleigh, a residual lead. Characterization, no verdict, no matched null.
Float carve-out: |U| analytic-size, integer args, no key in arg path.
"""
import math
import numpy as np
from eps_to_d_run_v1 import prime_order_curve, full_orbit, padd


def coords(p, m, G):
    xs = full_orbit(G, p, m); ys = [None] * m; acc = None
    for d in range(1, m):
        acc = padd(acc, G, p); ys[d] = acc[1]
    return xs, ys


def U_row(xs, ys, b, c, p, n):
    idx = [d for d in range(1, n) if xs[d] is not None]
    arg = np.array([(b * xs[d] + c * ys[d]) % p for d in idx], dtype=float)
    ph = np.zeros(n, dtype=complex); ph[idx] = np.exp(2j * np.pi * arg / p)
    return np.fft.fft(ph)


def princ_ratio_and_residual(U):
    z = U[1:]                                   # a != 0
    pts = np.column_stack([z.real, z.imag])
    pts = pts - pts.mean(0)
    cov = pts.T @ pts / len(pts)
    w, V = np.linalg.eigh(cov)                   # w[0] <= w[1]
    lam2, lam1 = w[0], w[1]
    minor = pts @ V[:, 0]                        # residual = projection onto minor axis
    return lam2 / lam1 if lam1 > 0 else 1.0, np.abs(minor)


def tail_k(mags, grid):
    mags = np.sort(np.asarray(mags)); N = len(mags); xs, ys = [], []
    sc = mags.mean() or 1.0
    for e in grid:
        f = np.searchsorted(mags, e * sc) / N
        if f > 0:
            xs.append(math.log(e)); ys.append(math.log(f))
    return float(np.polyfit(np.array(xs), np.array(ys), 1)[0]) if len(xs) >= 2 else float('nan')


def main():
    grid = [0.05, 0.08, 0.12, 0.18, 0.25, 0.35]
    print("y-axis (b=0) dimensionality + residual tail, vs x-axis (c=0) reference.\n")
    print(f"  {'p':>5} {'yaxis λ2/λ1':>12} {'yaxis resid-k':>14} {'xaxis λ2/λ1':>12} {'xaxis resid-k':>14}")
    for (lo, hi) in [(547, 548), (1303, 1304), (2089, 2090)]:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, n, G = r
        xs, ys = coords(p, n, G)
        yr, yk, xr, xk = [], [], [], []
        for c in range(1, min(30, p)):
            ratio, resid = princ_ratio_and_residual(U_row(xs, ys, 0, c, p, n))
            yr.append(ratio); yk.extend(resid.tolist())
            ratio2, resid2 = princ_ratio_and_residual(U_row(xs, ys, c, 0, p, n))
            xr.append(ratio2); xk.extend(resid2.tolist())
        print(f"  {p:>5} {np.mean(yr):>12.4f} {tail_k(yk, grid):>14.3f} "
              f"{np.mean(xr):>12.4f} {tail_k(xk, grid):>14.3f}")
    print("\n  y λ2/λ1 → 0 = 1-D forced line; then resid-k → 2 means the OFF-LINE part is Rayleigh")
    print("  (fully forced, dead end); resid-k < 2 means the residual keeps structure (a lead).")
    print("  x-axis should show λ2/λ1 ≈ 1 (2-D isotropic Rayleigh) as the contrast.")


if __name__ == "__main__":
    main()
