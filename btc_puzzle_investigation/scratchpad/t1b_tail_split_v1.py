#!/usr/bin/env python3
"""
t1b_tail_split_v1.py — gate-free CHARACTERIZATION: does the sub-Rayleigh tail exponent k of |U(a,b,c)|
differ by GEOMETRY — c=±b diagonal vs the axes (c=0, b=0) vs generic (b,c)? Localizes the non-Gaussian
structure. Extends RESULT_t1b0 (pooled k≈1.4). Not a matched-null verdict; distributional-shape fit.
Float carve-out: |U| magnitudes, integer args in the sum, no key in the arg path, no verdict.
"""
import math
import numpy as np
from eps_to_d_run_v1 import prime_order_curve, full_orbit, padd, tonelli


def coords(p, m, G):
    xs = full_orbit(G, p, m)
    ys = [None] * m
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


def tail_k(mags, grid):
    mags = np.sort(np.asarray(mags))
    N = len(mags)
    xs, ys = [], []
    for e in grid:
        f = np.searchsorted(mags, e) / N
        if f > 0:
            xs.append(math.log(e)); ys.append(math.log(f))
    if len(xs) < 2:
        return float('nan')
    return float(np.polyfit(np.array(xs), np.array(ys), 1)[0])


def main():
    rng = np.random.default_rng(1)
    grid = [0.05, 0.08, 0.12, 0.18, 0.25, 0.35]
    print("Tail exponent k by GEOMETRY (Rayleigh 2; sub-Rayleigh real 1). Pooled |U(a,b,c)|/sqrt(n), a!=0.\n")
    print(f"  {'p':>5} {'axis c=0':>9} {'axis b=0':>9} {'diag c=±b':>10} {'generic':>8} {'random':>8}")
    for (lo, hi) in [(547, 548), (1303, 1304), (2089, 2090)]:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, n, G = r
        xs, ys = coords(p, n, G)
        bs = list(range(1, min(30, p)))
        cls = {"c0": [], "b0": [], "diag": [], "gen": [], "rand": []}
        for b in bs:
            cls["c0"].extend((np.abs(U_row(xs, ys, b, 0, p, n)[1:]) / math.sqrt(n)).tolist())
            cls["b0"].extend((np.abs(U_row(xs, ys, 0, b, p, n)[1:]) / math.sqrt(n)).tolist())
            cls["diag"].extend((np.abs(U_row(xs, ys, b, b, p, n)[1:]) / math.sqrt(n)).tolist())
            cls["diag"].extend((np.abs(U_row(xs, ys, b, (-b) % p, p, n)[1:]) / math.sqrt(n)).tolist())
            cg = int(rng.integers(1, p))
            cls["gen"].extend((np.abs(U_row(xs, ys, b, cg, p, n)[1:]) / math.sqrt(n)).tolist())
            ph = np.exp(2j * np.pi * rng.random(n))
            cls["rand"].extend((np.abs(np.fft.fft(ph)[1:]) / math.sqrt(n)).tolist())
        k = {name: tail_k(v, grid) for name, v in cls.items()}
        print(f"  {p:>5} {k['c0']:>9.3f} {k['b0']:>9.3f} {k['diag']:>10.3f} {k['gen']:>8.3f} {k['rand']:>8.3f}")
    print("\n  Read: if diag k is notably LOWER than the axes, the sub-Rayleigh (heavier near-zero)")
    print("  structure concentrates on the c=±b diagonal — a localization, not a verdict. If flat")
    print("  across geometries, the exponent is a global property of the curve char sums.")


if __name__ == "__main__":
    main()
