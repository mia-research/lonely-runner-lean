#!/usr/bin/env python3
# Exploratory follow-up: DIRECTION + magnitude of the b=0 (pure-y) axis deficit found by
# harmonic_deficit_locus_v2.py. Not a new test -- characterizes the sign of the located locus.
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords
from harmonic_deficit_locus_v2 import build_U, R

def check(p, n, G, rng):
    xs, ys = group_coords(G, p, n, 0)
    xi = np.array(xs[1:], dtype=np.int64) % p; yi = np.array(ys[1:], dtype=np.int64) % p
    d = np.arange(1, n)
    aUc = np.abs(build_U(xi, yi, np.exp(2j * np.pi * d / n), p))
    acc = np.zeros((p, p))
    for _ in range(R):
        acc += np.abs(build_U(xi, yi, np.exp(2j * np.pi * rng.random(n - 1)), p))
    Er = acc / R
    D = aUc - Er
    BB, CC = np.meshgrid(np.arange(p), np.arange(p), indexing='ij')
    axis = (BB == 0) & (CC != 0)                 # b=0, c!=0  (pure-y harmonics)
    off = (BB != 0)                              # off-axis (has x-dependence)
    # per-harmonic deficit as % of the random-ensemble mean magnitude on each set
    ax_def = 100 * D[axis].mean() / Er[axis].mean()
    off_def = 100 * D[off].mean() / Er[off].mean()
    # also the raw magnitudes to rule out a scale artifact (D already per-harmonic char-minus-rand)
    print(f"  p={p:5d}: axis(b=0) deficit={ax_def:+.3f}%  off-axis deficit={off_def:+.3f}%  "
          f"ratio={ax_def/off_def:5.1f}x   |mean|U|_char axis={aUc[axis].mean():.3f} rand={Er[axis].mean():.3f}", flush=True)

def main():
    rng = np.random.default_rng(20260721)
    for p0 in (433, 577, 991):
        r = prime_order_curve(p0, p0 + 40)
        if r: check(*r, rng)

if __name__ == "__main__":
    main()
