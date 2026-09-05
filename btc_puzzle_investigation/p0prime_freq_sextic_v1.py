#!/usr/bin/env python3
"""
p0prime_freq_sextic_v1.py -- does the low-mode excess localize in FREQUENCY (b,c)
space, and specifically on the sextic/mu6 character classes of the frequency?

S5 tested mu6-orbits of the index a and found the excess DISTRIBUTED there.  The
p=991 exhaustive-vs-subsample gap (7.49% vs 7.08%) hinted the excess may live on
specific (b,c).  Here: per-frequency excess = charN_LOW(b,c) - mean_null N_LOW,
then BIN by the sextic character class of b and of c (chi6(x)=x^((p-1)/6), the
natural CM-structured feature for j=0), and test whether classes differ.

  uniform across classes  -> excess is not sextic-localized (global)
  classes differ (chi^2)  -> the excess concentrates on a sextic subclass of
                             frequencies -> arrangement structure tied to the
                             sextic/CM character (a real lever-direction)

Exploratory characterization; float FFT/chi^2 reported, low-mode counts exact.
"""
import argparse
import numpy as np
from row_budget_run_v1 import load_freqs, mu6_orbits, Permuter, SPEC_N, SPEC_BETA
from row_budget_core_v1 import curve_orbit

THRESH = 0.01   # noqa: float


def sextic_class(vals, p):
    """chi6(x) = x^((p-1)/6) mod p, mapped to a class 0..5 by matching zeta6^k."""
    g = 1
    # zeta6 = a primitive 6th root: use the group of 6th roots
    # build map {value -> k}
    from sympy import primitive_root
    z6 = pow(int(primitive_root(p)), (p - 1) // 6, p)
    roots = {}
    x = 1
    for k in range(6):
        roots[x] = k
        x = x * z6 % p
    out = np.array([roots[pow(int(v) % p, (p - 1) // 6, p)] if v % p != 0 else -1
                    for v in vals], dtype=np.int64)
    return out


def run(p, freqs, R, rng):
    X, Y, n = curve_orbit(p); assert n == SPEC_N[p]
    beta = SPEC_BETA[p]
    xb = beta * X[1] % p
    lam = int(np.nonzero((X == xb) & (Y == Y[1]))[0][0])
    reps6, orb6, unit6, pw6 = mu6_orbits(n, lam)
    P6 = Permuter(n, reps6, orb6, unit6, pw6)
    tab = np.exp(2j * np.pi * np.arange(p) / p)          # noqa: float
    F = freqs[p]
    B = np.array([b for b, c in F]); C = np.array([c for b, c in F])
    cb = sextic_class(B, p); cc = sextic_class(C, p)

    char_nl = np.zeros(len(F), dtype=np.int64)
    null_nl = np.zeros(len(F))                            # noqa: float (mean over R)
    for i, (b, c) in enumerate(F):
        e = (b * X + c * Y) % p
        s = tab[e]; s[0] = 0.0                            # noqa: float
        rows = [s] + [s[P6.draw(rng)] for _ in range(R)]
        U2 = np.abs(np.fft.fft(np.array(rows), axis=1)) ** 2   # noqa: float
        rho = U2 / (n - 1)                               # noqa: float
        low = rho[:, 1:] < THRESH
        char_nl[i] = int(low[0].sum())
        null_nl[i] = low[1:].sum() / R                   # noqa: float
    exc = char_nl - null_nl                              # noqa: float per-freq excess
    tot_exc = float(exc.sum()); tot_char = int(char_nl.sum())   # noqa: float

    print(f"\n  p={p} n={n} m={len(F)}  total excess "
          f"{100*tot_exc/ (tot_char-tot_exc):.2f}%")   # noqa: float
    # concentration of positive excess across individual freqs
    pos = np.clip(exc, 0, None)                           # noqa: float
    k10 = max(1, len(F) // 10)
    share = float(np.sort(pos)[::-1][:k10].sum() / max(pos.sum(), 1e-30))  # noqa: float
    print(f"    top-10% freqs carry {100*share:.1f}% of positive excess (uniform 10%)")

    for name, cls in (("chi6(b)", cb), ("chi6(c)", cc)):
        print(f"    excess by {name} class:")
        exps = []
        obss = []
        for k in range(6):
            m = cls == k
            if m.sum() == 0:
                continue
            e_k = float(exc[m].sum()); c_k = int(char_nl[m].sum())   # noqa: float
            base = c_k - e_k
            pct = 100 * e_k / base if base > 0 else 0.0  # noqa: float
            exps.append(m.sum()); obss.append(e_k)
            print(f"      class {k}: n_freq={int(m.sum()):>5}  excess={pct:>6.2f}%")
        # chi^2: is per-class excess proportional to class size (=uniform)?
        exps = np.array(exps, dtype=float); obss = np.array(obss)  # noqa: float
        E = tot_exc * exps / exps.sum()                  # noqa: float
        keep = E > 0
        chi2 = float(np.sum((obss[keep] - E[keep]) ** 2 / E[keep]))  # noqa: float
        df = int(keep.sum()) - 1
        z = (chi2 - df) / np.sqrt(2 * df) if df > 0 else 0.0   # noqa: float
        print(f"      -> class-uniformity chi2={chi2:.1f} df={df}  z={z:+.1f}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", default="163,211,349")
    ap.add_argument("--R", type=int, default=64)
    ap.add_argument("--seed", type=int, default=20260830)
    a = ap.parse_args()
    freqs, h = load_freqs()
    print(f"freq/sextic localization  freq sha {h[:16]}...  R={a.R}")
    rng = np.random.default_rng(a.seed)
    for p in [int(t) for t in a.primes.split(",")]:
        run(p, freqs, a.R, rng)


if __name__ == "__main__":
    main()
