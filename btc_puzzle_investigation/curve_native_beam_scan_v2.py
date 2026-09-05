#!/usr/bin/env python3
"""
curve_native_beam_scan_v2.py -- EXPLORATORY.  Supersedes v1's NULL only.

WHY v2 EXISTS.  v1 used a FREE orbit permutation as its null.  That destroys the forced
symmetries of the readout, and it produced a phantom: [I] chi2y scored ge=0/6 (apparent
signal) under the free null and ge=5/6 (null) on IDENTICAL data under the symmetry-
preserving null of phase_family_scan_v1.py.  Textbook feedback_residue_vs_component_
tautology.  v1's panels are hereby NOT ADJUDICATED; this file re-runs them.

THE FIX -- a GENERIC symmetry-preserving null.  Each curve-native readout has its own
forced covariance under the two group actions, and the null must preserve BOTH:

    negation  d -> -d      x_{-d} = x_d,  y_{-d} = -y_d
    GLV/mu3   d -> lam d   x_{lam d} = beta x_d,  y_{lam d} = y_d   (beta^3 = 1)

  => chi2(y)      : c_lam = +1              c_neg = -1     (mu3-invariant, ODD)
     chi6(x)      : c_lam = chi6(beta)      c_neg = +1     (mu6-covariant, EVEN)
     chi2y*chi6x  : c_lam = chi6(beta)      c_neg = -1
     sextant      : as chi6(x)

These multipliers are MEASURED from the data as exact ratios and CHECKED for constancy
(C-COV) before use -- if a readout is not covariant the run says so instead of guessing.
The null then permutes the L = (n-1)/6 free class values and rebuilds through the SAME
multipliers, destroying only the arrangement.

Object unchanged from v1:  H(k,a) = sum_d R(d) e_n(phi_k(d) + a d),  phi in {k d^2, k d^-1}.
k=0 is the closure-covered column (bounded-degree readout x character phase, provably at
the floor); any signal must appear at k != 0.
"""
import argparse, json, sys
import numpy as np
from sympy import primitive_root
from twist_orbit_spectrum_run_v1 import signal
from curve_native_beam_scan_v1 import readouts, base_table, plane_maxima


def orbit_structure(n):
    """g, powg (g^m), L, and a cube root lam of 1 mod n."""
    g = int(primitive_root(n))
    powg = np.empty(n - 1, dtype=np.int64)
    cur = 1
    for m in range(n - 1):
        powg[m] = cur
        cur = (cur * g) % n
    L = (n - 1) // 6
    lam = pow(g, (n - 1) // 3, n)
    return g, powg, L, lam


def covariance_multipliers(R, n, lam, tol=1e-9):
    """Measure c_lam = R(lam d)/R(d) and c_neg = R(-d)/R(d); check constancy (C-COV)."""
    d = np.arange(1, n, dtype=np.int64)
    nz = np.abs(R[d]) > tol
    dd = d[nz]
    cl = R[(lam * dd) % n] / R[dd]
    cn = R[(n - dd) % n] / R[dd]
    ok = (np.std(cl) < 1e-6) and (np.std(cn) < 1e-6)
    return complex(np.mean(cl)), complex(np.mean(cn)), bool(ok), \
        float(np.std(cl)), float(np.std(cn))


def sym_perm_null(R, n, powg, L, c_lam, c_neg, rng):
    """Permute the L free class values; rebuild through the measured multipliers.
    Class m of the multiplicative index: g^m, m = 0..n-2; the mu6 grading is m // L."""
    vals = R[powg[:L]].copy()
    vals = vals[rng.permutation(L)]
    m = np.arange(n - 1)
    blk = m // L                       # 0..5 : which mu6 coset
    # coset j is reached by lam^(j mod 3) and a negation when j >= 3
    mult = (c_lam ** (blk % 3)) * np.where(blk >= 3, c_neg, 1.0)
    out = np.zeros(n, dtype=complex)
    out[powg] = mult * vals[m % L]
    return out


def run(p, fams, n_null, rng):
    s = signal(p, 7)
    if s is None:
        return None
    n, c, X, Y = s
    Rs = readouts(p, n, c, X, Y)
    g, powg, L, lam = orbit_structure(n)
    print(f"p={p} n={n} L={L} lam={lam}")
    rec = {"p": p, "n": int(n), "L": int(L)}
    for name, R in Rs.items():
        cl, cn, ok, sl, sn_ = covariance_multipliers(R, n, lam)
        rec[f"COV:{name}"] = {"c_lam": [cl.real, cl.imag], "c_neg": [cn.real, cn.imag],
                              "ok": ok, "sd_lam": sl, "sd_neg": sn_}
        print(f"  C-COV {name:14s} c_lam={cl:.4f} (sd {sl:.1e})  "
              f"c_neg={cn:+.4f} (sd {sn_:.1e})  ok={ok}")
        if not ok:
            print(f"     -> NOT covariant; no valid class null; SKIPPED")
            continue
        for fam in fams:
            base = base_table(fam, n)
            Rk = plane_maxima(R, n, base)
            knz = Rk[1:]
            mx = []
            for _ in range(n_null):
                Rn = sym_perm_null(R, n, powg, L, cl, cn, rng)
                mx.append(float(plane_maxima(Rn, n, base)[1:].max()))   # noqa: float
            ge = sum(1 for v in mx if v >= knz.max())
            rec[f"{fam}:{name}"] = {
                "R0": float(Rk[0]), "max": float(knz.max()),            # noqa: float
                "med": float(np.median(knz)),                           # noqa: float
                "R0_pctile": float(100.0 * (knz < Rk[0]).mean()),       # noqa: float
                "null_mean": float(np.mean(mx)), "null_max": float(np.max(mx)),
                "ge": ge, "nnull": n_null}
            r = rec[f"{fam}:{name}"]
            print(f"    [{fam}] R0={r['R0']:7.2f} (pctile {r['R0_pctile']:5.1f}%) "
                  f"med={r['med']:6.2f} max={r['max']:7.2f}  null "
                  f"{r['null_mean']:6.2f}/{r['null_max']:6.2f}  ge={ge}/{n_null}")
            sys.stdout.flush()
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", type=int, nargs="+", default=[823, 1303, 1831])
    ap.add_argument("--fams", nargs="+", default=["Q", "I"])
    ap.add_argument("--nnull", type=int, default=12)
    ap.add_argument("--seed", type=int, default=20260730)
    ap.add_argument("--out", default="curve_native_beam_scan_v2.json")
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    res = [r for r in (run(p, a.fams, a.nnull, rng) for p in a.primes) if r]
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"\nwrote {a.out}")


if __name__ == "__main__":
    main()
