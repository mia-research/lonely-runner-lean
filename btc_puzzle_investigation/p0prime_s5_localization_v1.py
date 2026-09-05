#!/usr/bin/env python3
"""
p0prime_s5_localization_v1.py -- the FORK test for the ~7% low-mode excess.

Question: is the excess of low-rho modes (real curve over MN-mu6 null) spread
UNIFORMLY across the mu6-orbits of the frequency index a, or CONCENTRATED on
specific orbits?
  - uniform  -> char low-set is just a scaled-up copy of the null low-set shape
                -> leans "forced global marginal" (a distributed CM signature)
  - localized-> char low-set is RESHAPED vs the null -> an unprojected-subspace
                effect, the kind of arrangement structure that could be a lever

Statistic (per prime): chi^2 testing char_orbit vs the null SHAPE.
  E_o = char_tot * (null_orbit_o / null_tot)   [null shape, scaled to char mass]
  chi2 = sum_o (char_orbit_o - E_o)^2 / E_o ,  df = norb - 1
  z_shape = (chi2 - df) / sqrt(2 df)
z_shape ~ 0  => uniform excess (char is null-shaped).
z_shape >> 0 => localized excess (char reshaped) -> report which orbits carry it.

This is EXPLORATORY characterization (S5 was pre-named as a next-prereg object in
PREREG_row_budget_lowtail_v1.md); the float FFT / chi^2 are reported statistics,
not a threshold on keyed data.  The low-set membership counts are exact integers.
"""
import argparse
import numpy as np
from row_budget_run_v1 import (load_freqs, mu6_orbits, Permuter, SPEC_N, SPEC_BETA)
from row_budget_core_v1 import curve_orbit

THRESH = 0.01   # noqa: float


def run(p, freqs, R, rng):
    X, Y, n = curve_orbit(p)
    assert n == SPEC_N[p]
    beta = SPEC_BETA[p]
    xb = beta * X[1] % p
    lam = int(np.nonzero((X == xb) & (Y == Y[1]))[0][0])
    reps6, orb6, unit6, pw6 = mu6_orbits(n, lam)
    P6 = Permuter(n, reps6, orb6, unit6, pw6)
    norb = len(reps6)
    orb = orb6[1:]                                     # mu6-orbit of each a=1..n-1
    tab = np.exp(2j * np.pi * np.arange(p) / p)        # noqa: float
    F = freqs[p]

    char_orbit = np.zeros(norb)                        # noqa: float (integer-valued)
    null_orbit = np.zeros(norb)                        # noqa: float (summed over R)
    char_tot = 0
    null_tot = 0
    for (b, c) in F:
        e = (b * X + c * Y) % p
        s = tab[e]; s[0] = 0.0                          # noqa: float
        rows = [s] + [s[P6.draw(rng)] for _ in range(R)]
        U2 = np.abs(np.fft.fft(np.array(rows), axis=1)) ** 2      # noqa: float
        rho = U2 / (n - 1)                              # noqa: float
        low = rho[:, 1:] < THRESH                       # (R+1, n-1) bool
        char_low = low[0].astype(np.int64)
        null_low_count = low[1:].sum(0).astype(np.int64)          # per-a, 0..R
        char_orbit += np.bincount(orb, weights=char_low, minlength=norb)      # noqa: float
        null_orbit += np.bincount(orb, weights=null_low_count, minlength=norb)  # noqa: float
        char_tot += int(char_low.sum())
        null_tot += int(null_low_count.sum())

    # shape test: is char just a scaled-up null shape?
    null_shape = null_orbit / null_tot                  # noqa: float
    E = char_tot * null_shape                           # noqa: float
    keep = E > 0
    chi2 = float(np.sum((char_orbit[keep] - E[keep]) ** 2 / E[keep]))   # noqa: float
    df = int(keep.sum()) - 1
    z_shape = (chi2 - df) / np.sqrt(2 * df)             # noqa: float

    # per-orbit standardized excess (Poisson-ish) to see localization
    null_avg = null_orbit / R                           # noqa: float  expected char per orbit
    exc = char_orbit - null_avg                         # noqa: float
    zo = exc / np.sqrt(np.maximum(null_avg, 1.0))       # noqa: float
    order = np.argsort(zo)[::-1]
    top = order[:5]
    excess_frac = float(exc.sum() / char_tot)           # noqa: float
    # concentration: share of TOTAL positive excess carried by the top 10% of orbits
    pos = np.clip(exc, 0, None)                          # noqa: float
    k10 = max(1, norb // 10)
    top_share = float(np.sort(pos)[::-1][:k10].sum() / max(pos.sum(), 1e-30))  # noqa: float
    uniform_share = k10 / norb                           # noqa: float
    return dict(p=p, n=int(n), norb=norb, char_tot=char_tot,
                null_tot_avg=null_tot / R, excess_frac=excess_frac,   # noqa: float
                z_shape=float(z_shape), chi2=chi2, df=df,   # noqa: float
                top_share=top_share, uniform_share=uniform_share,
                zo_top=[round(float(zo[o]), 2) for o in top])   # noqa: float


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", default="163,211,349,433,577")
    ap.add_argument("--R", type=int, default=64)
    ap.add_argument("--seed", type=int, default=20260828)
    a = ap.parse_args()
    freqs, h = load_freqs()
    print(f"S5 localization  freq sha {h[:16]}...  R={a.R} seed={a.seed}")
    print("z_shape~0 => uniform excess (forced-ish); z_shape>>0 => localized (lever-ish)")
    rng = np.random.default_rng(a.seed)
    import time
    for p in [int(t) for t in a.primes.split(",")]:
        t0 = time.time()
        o = run(p, freqs, a.R, rng)
        print(f"\n  p={o['p']} n={o['n']} norb={o['norb']}  [{int(time.time()-t0)}s]")
        print(f"    char_low={o['char_tot']}  null_low(avg)={o['null_tot_avg']:.0f}  "
              f"excess={100*o['excess_frac']:.2f}%")
        print(f"    z_shape = {o['z_shape']:+.1f}   (chi2={o['chi2']:.0f}, df={o['df']})")
        print(f"    top-10%-orbit share of positive excess = {100*o['top_share']:.1f}% "
              f"(uniform would be {100*o['uniform_share']:.1f}%)")
        print(f"    top-5 orbit excess z: {o['zo_top']}")


if __name__ == "__main__":
    main()
