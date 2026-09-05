#!/usr/bin/env python3
"""
chirp_hologram_scan_v1.py  --  EXPLORATORY.  No verdict, no grade, no leakage claim.

THE OBJECT (new to this record):  the quadratic-phase ("chirp") plane

    H(k,a) = sum_{d in Z/n} c(d) * e_n(k*d^2 + a*d),     c(d) = chi2(y of [d]G)

The record's entire twist-orbit programme is the k=0 LINE of this plane:
H(0,a) = V(-a).  Every statistic in the record (magnitude spectrum, additive /
multiplicative autocorrelation, bispectrum, monodromy moments) is built from
that line.

WHY THE PLANE IS NOT COVERED BY THE RECORD'S BOUNDS
  * spectral_concentration_closure_v1.md bounds Corr_F(a) = (1/n) sum_d F([d]G) e_n(-ad):
    a LINEAR phase in d, i.e. a character of Z/n.  e_n(k d^2) is NOT a character of Z/n,
    so that estimate does not apply to k != 0.
  * The Wiener-norm route is vacuous here.  The record already proved (row_budget
    PREREG_row_budget_lowtail_v1.md F8) that the chirp's spectrum is FLAT at modulus
    sqrt(n): |Ghat(a)| in [sqrt(n)-1, sqrt(n)+1] for every a.  Hence ||chirp||_A = sqrt(n),
    and |H(k,a)| <= ||chirp||_A * max|V| <= sqrt(n)*2sqrt(p) ~ 2p, against a TRIVIAL
    bound of n ~ p.  Vacuous.
  * A quadratic-phase sequence has a flat magnitude spectrum and a delta autocorrelation
    -- the exact fingerprint the record reports as "maximally structureless subject to
    mu3 + odd + purity".  A chirp is invisible to every statistic in the record.

FORCED STRUCTURE OF THE PLANE (exact, checked as controls, NOT findings)
  F1  c(n-d) = -c(d)          =>  H(k,-a) = -H(k,a)   and   H(k,0) = 0 for every k.
  F2  c(lam*d) = c(d), lam^3=1 (GLV/mu3)  =>  H(k*lam^2, a*lam) = H(k,a).
  F3  k=0 line is V, so max_a |H(0,a)| <= 2 sqrt(p) is the record's cap.
  => effective independent cells ~ n^2/6, not n^2.  Nulls below preserve F1+F2 so the
     max-comparison is like-for-like.

READOUT (characterization only):
  R(k) = max_a |H(k,a)|^2 / n      ("beam response" at chirp rate k; R ~ O(1) if generic)
  reported: R(0) (= the record's line, expect ~4p/n ~ 4 via the cap), max_{k!=0} R(k),
  and the same for each null / control.  A GROWING max_{k!=0} R with n is the only thing
  that would be interesting; a flat one is a bounded magnitude, not a closure.

EXACTNESS.  Signal path (legendre, orbit, d^2 mod n, index maps) is exact int.  Float
appears only in the FFT magnitudes, ranked against the null draws -- never a threshold
on data.  Same carve-out as twist_orbit_spectrum_run_v1.py.
"""
import argparse, json, sys
import numpy as np
from sympy import isprime, primitive_root
from twist_orbit_spectrum_run_v1 import signal, legendre
from row_budget_core_v1 import curve_orbit


# ---------------------------------------------------------------- exact helpers
def cube_roots_of_unity(n):
    """lam with lam^3 = 1 mod n, lam != 1 (exists iff n = 1 mod 3). Exact."""
    if (n - 1) % 3:
        return []
    g = int(primitive_root(n))
    lam = pow(g, (n - 1) // 3, n)
    return [lam, (lam * lam) % n]


def chirp_plane_maxima(c, n, ktable=None):
    """R(k) = max_{a} |sum_d c(d) e_n(k d^2 + a d)|^2 / n, for every k in Z/n.

    One FFT per k.  Returns (R, argmax_a) arrays of length n."""
    d = np.arange(n, dtype=np.int64)
    q = (d * d) % n                                   # exact int
    E = np.exp(2j * np.pi * np.arange(n) / n)         # noqa: float (root-of-unity table)
    cc = c.astype(np.complex128)                      # noqa: float
    R = np.empty(n)                                   # noqa: float
    A = np.empty(n, dtype=np.int64)
    ks = range(n) if ktable is None else ktable
    for k in ks:
        idx = (k * q) % n                             # exact int index
        Hk = np.fft.fft(cc * E[idx])                  # noqa: float
        pw = Hk.real ** 2 + Hk.imag ** 2              # |.|^2, no sqrt
        j = int(np.argmax(pw))
        R[k] = pw[j] / n                              # noqa: float
        A[k] = j
    return R, A


# ---------------------------------------------------------------- nulls
def null_class_perm(c, n, rng):
    """Permute the mu6-class values, rebuild by the FORCED mu3+odd symmetry.
    Preserves F1 and F2 exactly (the pipeline's own null)."""
    g = int(primitive_root(n))
    powg = np.zeros(n - 1, dtype=np.int64)
    cur = 1
    for m in range(n - 1):
        powg[m] = cur
        cur = (cur * g) % n
    L = (n - 1) // 6
    vals = c[powg[:L]].copy()
    vals = vals[rng.permutation(L)]
    m = np.arange(n - 1)
    sign = np.where((m // L) % 2 == 0, 1, -1)
    W = sign * vals[m % L]
    out = np.zeros(n, dtype=np.int64)
    out[powg] = W
    out[0] = 0
    return out


def null_odd_random(c, n, rng):
    """Random +-1 with c(n-d) = -c(d), c(0)=0.  Preserves F1 only (looser null)."""
    out = np.zeros(n, dtype=np.int64)
    h = (n - 1) // 2
    s = rng.integers(0, 2, size=h) * 2 - 1
    out[1:h + 1] = s
    out[n - 1:n - h - 1:-1] = -s
    return out


# ---------------------------------------------------------------- controls
def matched_odd_chirp(n, kappa, a0):
    """The BEST real, ODD, +-1 sequence for the cell (kappa, a0).

    Pairing d with -d and using c(-d) = -c(d):
        H(k,a) = sum_{d=1}^{(n-1)/2} c(d) * e_n(k d^2) * 2i*sin(2 pi a d / n)
    so the optimal real +-1 choice is the sign of the real part of each term.
    This is the correct plant: the forced ODDNESS means a sequence cannot track a
    chirp's phase directly (e_n(k d^2) is EVEN, the sign is all c has), so the naive
    sign(Re e_n(k d^2 + a0 d)) plant does NOT align -- it was the v1 control's bug.
    """
    h = (n - 1) // 2
    d = np.arange(1, h + 1, dtype=np.int64)
    term = np.exp(2j * np.pi * ((kappa * d * d) % n) / n) * \
        (1j * np.sin(2 * np.pi * ((a0 * d) % n) / n))      # noqa: float (control target)
    s = np.sign(term.real)                                  # noqa: float
    s[s == 0] = 1
    out = np.zeros(n, dtype=np.int64)
    out[1:h + 1] = s.astype(np.int64)
    out[n - 1:n - h - 1:-1] = -s.astype(np.int64)
    return out


def plant_chirp(c, n, kappa, a0, frac, rng):
    """C-PLANT: replace a fraction `frac` of the odd half-orbit by the matched odd
    chirp of cell (kappa, a0), keeping F1 exact.  frac=1 is the pure plant."""
    tgt = matched_odd_chirp(n, kappa, a0)
    h = (n - 1) // 2
    out = c.copy()
    sel = np.where(rng.random(h) < frac)[0] + 1
    out[sel] = tgt[sel]
    out[(n - sel) % n] = -tgt[sel]
    out[0] = 0
    return out


# ---------------------------------------------------------------- driver
def run_prime(p, n_null, rng, verbose=True):
    s = signal(p, 7)
    if s is None:
        return None
    n, c, X, Y = s
    out = {"p": p, "n": int(n)}

    # ---- exact forced-structure controls -----------------------------------
    d = np.arange(n, dtype=np.int64)
    out["C_ODD"] = bool(all(int(c[(n - i) % n]) == -int(c[i]) for i in range(1, n)))
    lams = cube_roots_of_unity(n)
    out["C_MU3_signal"] = bool(lams and all(
        np.array_equal(c[(lam * d) % n], c) for lam in lams))

    R, A = chirp_plane_maxima(c, n)
    out["R0"] = float(R[0])                            # noqa: float
    knz = np.arange(1, n)
    kbest = int(knz[np.argmax(R[knz])])
    out["Rmax_knz"] = float(R[kbest])                  # noqa: float
    out["kbest"] = kbest
    out["abest"] = int(A[kbest])
    # cap check on the k=0 line: |V|^2 <= 4p  =>  R0 <= 4p/n
    out["C_CAP_k0"] = bool(R[0] <= 4.0 * p / n + 1e-9)
    # F2 on the PLANE: R(k) = R(k lam^2)
    if lams:
        lam = lams[0]
        out["C_MU3_plane"] = float(np.max(np.abs(
            R[knz] - R[(knz * lam * lam) % n])))       # noqa: float

    # ---- nulls -------------------------------------------------------------
    for name, fn in (("class", null_class_perm), ("oddrand", null_odd_random)):
        mx = []
        for _ in range(n_null):
            cn = fn(c, n, rng)
            Rn, _ = chirp_plane_maxima(cn, n)
            mx.append(float(np.max(Rn[1:])))           # noqa: float
        out[f"null_{name}_mean"] = float(np.mean(mx))  # noqa: float
        out[f"null_{name}_max"] = float(np.max(mx))    # noqa: float
        out[f"null_{name}_ge"] = int(sum(1 for v in mx if v >= out["Rmax_knz"]))
        out[f"null_{name}_n"] = n_null

    # ---- C-PLANT: a planted chirp must light at its own k -------------------
    # POS: full-strength matched odd chirp must peak at k=kappa.
    # DILUTE: the fraction sweep gives the detection floor (what the scan can see).
    kappa, a0 = 7 % n, 3
    out["PLANT"] = {}
    for frac in (1.0, 0.5, 0.25, 0.12, 0.06):
        cp = plant_chirp(c, n, kappa, a0, frac, rng)
        Rp, _ = chirp_plane_maxima(cp, n)
        out["PLANT"][f"{frac}"] = {
            "R_at_kappa": float(Rp[kappa]),                       # noqa: float
            "kbest": int(np.argmax(Rp[1:]) + 1),
            "ratio_vs_null": float(Rp[kappa] / out["null_class_mean"]),  # noqa: float
        }
    out["PLANT_fires"] = bool(out["PLANT"]["1.0"]["kbest"] == kappa and
                              out["PLANT"]["1.0"]["R_at_kappa"] >
                              3 * out["null_class_mean"])
    # detection floor: smallest swept frac still peaking at kappa above 3x null
    flo = [f for f in (1.0, 0.5, 0.25, 0.12, 0.06)
           if out["PLANT"][f"{f}"]["kbest"] == kappa and
           out["PLANT"][f"{f}"]["R_at_kappa"] > 3 * out["null_class_mean"]]
    out["PLANT_floor_frac"] = min(flo) if flo else None

    if verbose:
        print(f"p={p:5d} n={n:5d} | C_ODD={out['C_ODD']} C_MU3={out['C_MU3_signal']} "
              f"C_CAP_k0={out['C_CAP_k0']} mu3plane_err={out.get('C_MU3_plane', -1):.2e}")
        print(f"    R(0) [record's line] = {out['R0']:.3f}   (cap allows {4*p/n:.3f})")
        print(f"    max_{{k!=0}} R = {out['Rmax_knz']:.3f} at k={kbest} a={out['abest']}")
        print(f"    null class  : mean {out['null_class_mean']:.3f} "
              f"max {out['null_class_max']:.3f}  ge={out['null_class_ge']}/{n_null}")
        print(f"    null oddrand: mean {out['null_oddrand_mean']:.3f} "
              f"max {out['null_oddrand_max']:.3f}  ge={out['null_oddrand_ge']}/{n_null}")
        pl = " ".join(f"{f}:{out['PLANT'][f]['ratio_vs_null']:.1f}x"
                      f"{'*' if out['PLANT'][f]['kbest'] == kappa else '-'}"
                      for f in ("1.0", "0.5", "0.25", "0.12", "0.06"))
        print(f"    C-PLANT k={kappa} (frac:ratio, *=peaks at kappa): {pl}")
        print(f"    C-PLANT fires={out['PLANT_fires']} floor_frac={out['PLANT_floor_frac']}")
        sys.stdout.flush()
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", type=int, nargs="+",
                    default=[823, 907, 967, 991, 1303, 1831])
    ap.add_argument("--nnull", type=int, default=12)
    ap.add_argument("--seed", type=int, default=20260730)
    ap.add_argument("--out", default="chirp_hologram_scan_v1.json")
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    res = []
    for p in args.primes:
        o = run_prime(p, args.nnull, rng)
        if o:
            res.append(o)
    json.dump(res, open(args.out, "w"), indent=1)
    print(f"\nwrote {args.out}  ({len(res)} primes)")


if __name__ == "__main__":
    main()
