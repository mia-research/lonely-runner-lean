#!/usr/bin/env python3
"""
curve_native_beam_scan_v1.py -- EXPLORATORY.  No verdict, no grade, no leakage claim.

THE POINT (why the previous two scans were the wrong beam family, and why this one
is not just "add chi6"):

  * spectral_concentration_closure_v1.md PROVES (given KS/Weil) that ANY readout
    F = psi o f with f rational of bounded degree on E has |Corr_F(a)| at the floor.
    chi6(x), chi2(y), the sextant/Eisenstein label, and every product of them ARE
    bounded-degree readouts.  => a curve-native readout against a CHARACTER phase
    e_n(a d) is INSIDE the closure, provably at the floor.  Testing it can only
    re-confirm a theorem.
  * The chirp scans escaped the closure (e_n(k d^2) is not a character of Z/n) but
    used arithmetic-generic beams with no curve structure in them.

  => The one combination that is BOTH curve-native AND outside the closure is the
     PRODUCT: a curve-native readout times a non-character phase in d.

        H(k,a) = sum_d  R(d) * e_n(phi_k(d) + a d),    R = curve-native readout

     R in { chi2(y)  [the twist, = the previous scans],
            chi6(x)  [the sextic],
            chi2(y)*chi6(x)  [the joint xy isotype -- the record's #1 open lead],
            zeta6^sextant(eis) [the Eisenstein/mu6 sextant label] }
     phi in { k d^2 (Q), k d^-1 (I -- the best-powered family measured) }.

  k=0 column of every panel = the closure-covered case, printed as an internal
  control: it MUST sit at the floor.  Any signal must appear at k != 0.

Exact int signal path (legendre, sextic index, orbit, index maps); float only in
FFT magnitudes ranked against permutation nulls.
"""
import argparse, json, sys
import numpy as np
from twist_orbit_spectrum_run_v1 import signal, legendre


def sextic_index(v, p, g6):
    """exact: j in 0..5 with v^((p-1)/6) = g6^j  (p = 1 mod 6). v != 0."""
    t = pow(int(v), (p - 1) // 6, p)
    cur = 1
    for j in range(6):
        if cur == t:
            return j
        cur = (cur * g6) % p
    return -1


def readouts(p, n, c, X, Y):
    """Return dict of curve-native readouts R(d), complex arrays of length n."""
    assert (p - 1) % 6 == 0
    from sympy import primitive_root
    g = int(primitive_root(p))
    g6 = pow(g, (p - 1) // 6, p)
    z6 = np.exp(2j * np.pi / 6)                                # noqa: float
    j6 = np.full(n, -1, dtype=np.int64)
    for d in range(1, n):
        xv = int(X[d]) % p
        if xv:
            j6[d] = sextic_index(xv, p, g6)
    chi6 = np.where(j6 >= 0, z6 ** np.maximum(j6, 0), 0)       # noqa: float
    chi2y = c.astype(np.complex128)                            # noqa: float
    # mu6 sextant label of x (the Eisenstein/sextant grading the record uses):
    # the sextic index IS the mu6 grading of x; keep it as an explicit panel.
    sext = np.where(j6 >= 0, z6 ** (np.maximum(j6, 0) % 6), 0)  # noqa: float
    return {"chi2y": chi2y, "chi6x": chi6,
            "chi2y_chi6x": chi2y * chi6, "sextant": sext}


def base_table(fam, n):
    d = np.arange(n, dtype=np.int64)
    if fam == "Q":
        return (d * d) % n
    if fam == "I":
        inv = np.zeros(n, dtype=np.int64)
        inv[1:] = np.array([pow(int(t), n - 2, n) for t in range(1, n)], dtype=np.int64)
        return inv
    raise ValueError(fam)


def plane_maxima(sig, n, base):
    E = np.exp(2j * np.pi * np.arange(n) / n)                  # noqa: float
    R = np.empty(n)                                            # noqa: float
    for k in range(n):
        H = np.fft.fft(sig * E[(base * k) % n])                # noqa: float
        R[k] = (H.real ** 2 + H.imag ** 2).max() / n           # noqa: float
    return R


def orbit_perm_null(sig, n, rng):
    """Permute the readout along the orbit (d != 0), preserving its value multiset.
    Destroys arrangement in d, keeps the marginal -- valid for both R and phi."""
    out = sig.copy()
    idx = rng.permutation(n - 1) + 1
    out[1:] = sig[idx]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", type=int, nargs="+", default=[823, 1303, 1831])
    ap.add_argument("--fams", nargs="+", default=["Q", "I"])
    ap.add_argument("--nnull", type=int, default=6)
    ap.add_argument("--seed", type=int, default=20260730)
    ap.add_argument("--out", default="curve_native_beam_scan_v1.json")
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    res = []
    for p in a.primes:
        s = signal(p, 7)
        if s is None:
            continue
        n, c, X, Y = s
        R = readouts(p, n, c, X, Y)
        rec = {"p": p, "n": int(n)}
        print(f"p={p} n={n}")
        for fam in a.fams:
            base = base_table(fam, n)
            for name, sig in R.items():
                Rk = plane_maxima(sig, n, base)
                knz = Rk[1:]
                mx = []
                for _ in range(a.nnull):
                    mx.append(float(plane_maxima(
                        orbit_perm_null(sig, n, rng), n, base)[1:].max()))  # noqa: float
                ge = sum(1 for v in mx if v >= knz.max())
                rec[f"{fam}:{name}"] = {
                    "R0": float(Rk[0]), "max": float(knz.max()),           # noqa: float
                    "med": float(np.median(knz)),                          # noqa: float
                    "R0_pctile": float(100.0 * (knz < Rk[0]).mean()),      # noqa: float
                    "null_mean": float(np.mean(mx)),                       # noqa: float
                    "null_max": float(np.max(mx)), "ge": ge, "nnull": a.nnull}
                r = rec[f"{fam}:{name}"]
                print(f"  [{fam}] {name:14s} R0={r['R0']:7.2f} "
                      f"(pctile {r['R0_pctile']:5.1f}%)  med={r['med']:6.2f}  "
                      f"max={r['max']:7.2f}   null {r['null_mean']:6.2f}/"
                      f"{r['null_max']:6.2f}  ge={ge}/{a.nnull}")
                sys.stdout.flush()
        res.append(rec)
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"\nwrote {a.out}")


if __name__ == "__main__":
    main()
