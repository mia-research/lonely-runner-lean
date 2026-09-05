#!/usr/bin/env python3
"""
p0prime_sextic_control_v1.py -- the FIRING CONTROL that p0prime_freq_sextic_v1.py
lacked.  Its class-uniformity chi^2/z has expected cells E_k proportional to the
total excess, so its null behaviour is undefined -- z=28 there is not validated.

Here: a proper PERMUTATION test of sextic localization on axis chi6(b).
  statistic T = variance across the 6 classes of the per-class excess RATE
                 rate_k = (class_k low-count) / (mean-null class_k low-count) - 1
  real      : char vs mean over M null replicates.
  pseudo j  : null replicate j vs mean over the OTHER M-1 replicates (exchangeable
              stand-in with NO real structure -> the correct null distribution).
  p = (#{ T_pseudo >= T_real } + 1) / (M + 1)     exact rank, no distributional
assumption.  If real T is NOT an outlier, the 'localization' is a statistic
artifact, not structure.

Exact low-mode counts; float rate/variance are ranked against the permutation
null (sanctioned pattern), not thresholded.
"""
import argparse
import numpy as np
from row_budget_run_v1 import load_freqs, mu6_orbits, Permuter, SPEC_N, SPEC_BETA
from row_budget_core_v1 import curve_orbit

THRESH = 0.01   # noqa: float


def sextic_class_arr(vals, p):
    from sympy import primitive_root
    z6 = pow(int(primitive_root(p)), (p - 1) // 6, p)
    roots = {}; x = 1
    for k in range(6):
        roots[x] = k; x = x * z6 % p
    return np.array([roots[pow(int(v) % p, (p - 1) // 6, p)] if v % p else -1
                     for v in vals], dtype=np.int64)


def run(p, F, M, rng):
    X, Y, n = curve_orbit(p); assert n == SPEC_N[p]
    beta = SPEC_BETA[p]; xb = beta * X[1] % p
    lam = int(np.nonzero((X == xb) & (Y == Y[1]))[0][0])
    reps6, orb6, unit6, pw6 = mu6_orbits(n, lam)
    P6 = Permuter(n, reps6, orb6, unit6, pw6)
    tab = np.exp(2j * np.pi * np.arange(p) / p)          # noqa: float
    cb = sextic_class_arr(np.array([b for b, c in F]), p)

    # per-class low-mode counts: row 0 = char, rows 1..M = null replicates.
    # The class is a property of the FREQUENCY (b,c) -- one class per freq.
    cls_counts = np.zeros((M + 1, 6), dtype=np.int64)
    for i, (b, c) in enumerate(F):
        e = (b * X + c * Y) % p
        s = tab[e]; s[0] = 0.0                           # noqa: float
        rows = [s] + [s[P6.draw(rng)] for _ in range(M)]
        U2 = np.abs(np.fft.fft(np.array(rows), axis=1)) ** 2   # noqa: float
        nl = ((U2 / (n - 1))[:, 1:] < THRESH).sum(1)     # noqa: float  (M+1,) per row
        cls_counts[:, cb[i]] += nl.astype(np.int64)

    def T(row_idx, null_rows):
        num = cls_counts[row_idx].astype(float)          # noqa: float
        den = cls_counts[null_rows].mean(0)              # noqa: float  mean null per class
        rate = num / np.maximum(den, 1.0) - 1.0          # noqa: float
        return float(np.var(rate))                       # noqa: float

    allnull = list(range(1, M + 1))
    T_real = T(0, allnull)
    T_ps = []
    for j in range(1, M + 1):
        others = [r for r in allnull if r != j]
        T_ps.append(T(j, others))
    T_ps = np.array(T_ps)                                # noqa: float
    ge = int((T_ps >= T_real).sum())
    pval = (ge + 1) / (M + 1)                            # noqa: float
    print(f"  p={p:>6} n={n:>6} m={len(F):>6} M={M}")
    print(f"    T_real = {T_real:.3e}   pseudo T: median {np.median(T_ps):.3e}  "  # noqa: float
          f"max {T_ps.max():.3e}")                        # noqa: float
    print(f"    permutation p = ({ge}+1)/({M}+1) = {pval:.4f}   "
          f"{'localization SURVIVES the control' if pval < 0.05 else 'NOT distinguishable from null -> artifact'}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", default="163,9319")
    ap.add_argument("--M", type=int, default=200)
    ap.add_argument("--seed", type=int, default=20260901)
    a = ap.parse_args()
    freqs, h = load_freqs()
    print(f"sextic localization FIRING CONTROL (chi6(b))  sha {h[:16]}...  M={a.M}")
    rng = np.random.default_rng(a.seed)
    for p in [int(t) for t in a.primes.split(",")]:
        run(p, freqs[p], a.M, rng)


if __name__ == "__main__":
    main()
