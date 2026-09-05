#!/usr/bin/env python3
"""N7 follow-up — the ONE new thing the finite-rank probe turned up:
the x-only spectrum U(b,0) appears to have a HARD near-zero FLOOR (zero values below 5% of RMS
at p=349,577,991), while the matched null has none. Measure min|U(b,0)|/RMS vs the null's.
Float: FFT carve-out, PREREG_subrayleigh_deficit_scaling_v1 §8; all statistics are ratios/ranks.  # noqa: float — (stat) sanctioned FFT carve-out; exact-int EC point set upstream
"""
import sys, numpy as np
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import subrayleigh_deficit_scaling_v1 as inst

def order(p):
    c = 1
    for x in range(p):
        r = (x*x % p * x + 7) % p
        c += 1 if r == 0 else (2 if pow(r, (p-1)//2, p) == 1 else 0)
    return c

def aU(pts, g, p):
    W = np.zeros((p, p), dtype=np.complex128)
    xs = np.fromiter((x for x, _ in pts), dtype=np.int64, count=len(pts))
    ys = np.fromiter((y for _, y in pts), dtype=np.int64, count=len(pts))
    np.add.at(W, (xs, ys), g)
    return np.abs(np.fft.fft2(W))  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision

print(f"{'p':>6} {'n':>6} | {'char min|U(b,0)|/RMS':>21} {'char min bulk':>14} | "
      f"{'null min c0 (mean/min over K)':>30}")
for p in (211, 349, 577, 991, 1471, 2089):
    n = order(p); G, pts = inst.all_points(p, n)
    A = aU(pts, inst.char_weight(n), p)
    c0 = A[:, 0][1:]; bulk = A[1:, 1:].ravel()
    rc = c0 / np.sqrt((c0*c0).mean()); rb = bulk / np.sqrt((bulk*bulk).mean())  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision
    K = 20
    nm = []
    for k in range(K):
        B = aU(pts, inst.null_weight(pts, n, seed=p*10**6+k), p)
        z = B[:, 0][1:]
        nm.append(float((z/np.sqrt((z*z).mean())).min()))  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision
    print(f"{p:>6} {n:>6} | {rc.min():>21.5f} {rb.min():>14.6f} | "
          f"mean {np.mean(nm):.5f}  min {np.min(nm):.5f}   "  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision
          f"ratio char/null_mean = {rc.min()/np.mean(nm):.1f}x", flush=True)  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision
