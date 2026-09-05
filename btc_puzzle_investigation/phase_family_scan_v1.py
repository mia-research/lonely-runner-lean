#!/usr/bin/env python3
"""
phase_family_scan_v1.py -- EXPLORATORY.  No verdict, no grade, no leakage claim.

Generalises chirp_hologram_scan_v1.py from the QUADRATIC phase to a FAMILY of
non-character phases.  For a phase family phi_k the object is

    H(k,a) = sum_d c(d) * e_n(phi_k(d) + a*d),    c(d) = chi2(y of [d]G)

k=0 is always the record's line (H(0,a) = V(-a)).  Families:

  Q   phi_k(d) = k d^2        quadratic  (EVEN in d)   -- chirp_hologram_scan_v1
  C   phi_k(d) = k d^3        cubic      (ODD  in d)
  I   phi_k(d) = k d^{-1}     inverse    (ODD  in d)   -- Kloosterman-type
  M   phi_k(m) = k m^2 in the MULTIPLICATIVE coordinate d = g^m (length n-1)

WHY THE PARITY OF THE PHASE IS THE POINT.  c is forced ODD.  Pairing d <-> -d:

  phi EVEN:  H(k,a) = sum_{d=1}^{h} c(d) * e_n(phi_k(d)) * 2i sin(2 pi a d/n)
             -> a +-1 sequence can only fix the SIGN, not the spinning phase
                e_n(phi_k(d));  best alignment ~ 0.16 n.
  phi ODD:   H(k,a) = sum_{d=1}^{h} c(d) * 2i sin(2 pi (phi_k(d) + a d)/n)
             -> the bracket is REAL, so a +-1 sequence CAN align every term;
                best alignment ~ (2/pi) n ~ 0.64 n.

=> ODD phase families admit ~4x stronger alignment, hence ~16x the power in R.
   The quadratic scan's weak power was a PARITY artifact, not a property of
   non-character phases.  This script tests that prediction (C-PARITY) and then
   scans all four families.

READOUT  R(k) = max_a |H(k,a)|^2 / n   (same as v1; generic => R ~ O(log n)).
NULLS    class-permutation (preserves forced mu3+odd) and odd-random.
PLANT    the matched odd sequence for the cell (k,a0), built generically from
         the pairing identity above -- correct for every family.

Exact int signal path; float only in FFT magnitudes ranked against null draws.
"""
import argparse, json, sys
import numpy as np
from sympy import primitive_root
from twist_orbit_spectrum_run_v1 import signal
from chirp_hologram_scan_v1 import null_class_perm, null_odd_random, cube_roots_of_unity


# ---------------------------------------------------------------- phase families
def phase_table(fam, n):
    """Return (N, base, ph) with ph[k][d] = phi_k(d) mod N as an int array factored
    as ph = k * base(d) mod N, plus the transform length N and the signal reindexer."""
    d = np.arange(n, dtype=np.int64)
    if fam == "Q":
        return n, (d * d) % n, "additive", "even"
    if fam == "C":
        return n, (d * d % n * d) % n, "additive", "odd"
    if fam == "I":
        inv = np.zeros(n, dtype=np.int64)
        inv[1:] = np.array([pow(int(t), n - 2, n) for t in range(1, n)], dtype=np.int64)
        return n, inv, "additive", "odd"
    if fam == "M":
        return n - 1, None, "multiplicative", "even"
    raise ValueError(fam)


def mult_coords(c, n):
    """w[m] = c(g^m), m = 0..n-2  (the multiplicative coordinate)."""
    g = int(primitive_root(n))
    powg = np.empty(n - 1, dtype=np.int64)
    cur = 1
    for m in range(n - 1):
        powg[m] = cur
        cur = (cur * g) % n
    return c[powg], powg


def plane_maxima(sig, N, base):
    """R(k) = max_a |sum_x sig(x) e_N(k*base(x) + a*x)|^2 / N, all k in Z/N."""
    E = np.exp(2j * np.pi * np.arange(N) / N)              # noqa: float
    ss = sig.astype(np.complex128)                         # noqa: float
    R = np.empty(N)                                        # noqa: float
    A = np.empty(N, dtype=np.int64)
    for k in range(N):
        H = np.fft.fft(ss * E[(k * base) % N])             # noqa: float
        pw = H.real ** 2 + H.imag ** 2
        j = int(np.argmax(pw))
        R[k] = pw[j] / N                                   # noqa: float
        A[k] = j
    return R, A


def matched_odd_plant(N, base, kappa, a0):
    """The best real ODD +-1 sequence for cell (kappa,a0), built from the pairing
    identity -- valid for ANY phase family (even or odd base)."""
    h = (N - 1) // 2
    x = np.arange(1, h + 1, dtype=np.int64)
    ph_p = (kappa * base[x] + a0 * x) % N
    ph_m = (kappa * base[(N - x) % N] - a0 * x) % N
    term = np.exp(2j * np.pi * ph_p / N) - np.exp(2j * np.pi * ph_m / N)   # noqa: float
    s = np.sign(term.real)                                 # noqa: float
    s[s == 0] = 1
    out = np.zeros(N, dtype=np.int64)
    out[1:h + 1] = s.astype(np.int64)
    out[N - 1:N - h - 1:-1] = -s.astype(np.int64)
    return out


def run(p, fams, n_null, rng):
    s = signal(p, 7)
    if s is None:
        return None
    n, c, X, Y = s
    res = {"p": p, "n": int(n)}
    for fam in fams:
        N, base, kind, par = phase_table(fam, n)
        if kind == "multiplicative":
            w, powg = mult_coords(c, n)
            m = np.arange(N, dtype=np.int64)
            base = (m * m) % N
            sig = w
        else:
            sig = c
        R, A = plane_maxima(sig, N, base)
        knz = np.arange(1, N)
        Rk = R[knz]
        rec = {"parity": par, "R0": float(R[0]),                       # noqa: float
               "Rmax_knz": float(Rk.max()), "kbest": int(knz[np.argmax(Rk)]),
               "med_knz": float(np.median(Rk)),                        # noqa: float
               "R0_pctile": float(100.0 * (Rk < R[0]).mean())}         # noqa: float
        # nulls
        mx = []
        for _ in range(n_null):
            cn = null_class_perm(c, n, rng)
            sg = mult_coords(cn, n)[0] if kind == "multiplicative" else cn
            Rn, _ = plane_maxima(sg, N, base)
            mx.append(float(np.max(Rn[1:])))                           # noqa: float
        rec["null_mean"] = float(np.mean(mx))                          # noqa: float
        rec["null_max"] = float(np.max(mx))                            # noqa: float
        rec["null_ge"] = int(sum(1 for v in mx if v >= rec["Rmax_knz"]))
        rec["null_n"] = n_null
        # C-PARITY / C-PLANT: matched odd plant at several strengths
        kappa, a0 = 7 % N, 3
        rec["plant"] = {}
        for frac in (1.0, 0.5, 0.25, 0.12):
            tgt = matched_odd_plant(N, base, kappa, a0)
            h = (N - 1) // 2
            cp = sig.copy()
            sel = np.where(rng.random(h) < frac)[0] + 1
            cp[sel] = tgt[sel]
            cp[(N - sel) % N] = -tgt[sel]
            cp[0] = 0
            Rp, _ = plane_maxima(cp, N, base)
            rec["plant"][f"{frac}"] = {
                "ratio": float(Rp[kappa] / rec["null_mean"]),          # noqa: float
                "peaks": bool(int(np.argmax(Rp[1:]) + 1) == kappa)}
        fl = [f for f in (1.0, 0.5, 0.25, 0.12)
              if rec["plant"][f"{f}"]["peaks"] and rec["plant"][f"{f}"]["ratio"] > 3]
        rec["floor"] = min(fl) if fl else None
        res[fam] = rec
        pl = " ".join(f"{f}:{rec['plant'][f]['ratio']:.1f}x"
                      f"{'*' if rec['plant'][f]['peaks'] else '-'}"
                      for f in ("1.0", "0.5", "0.25", "0.12"))
        print(f"  [{fam}] phi {par:4s} N={N:5d} | R0={rec['R0']:6.2f} "
              f"(pctile {rec['R0_pctile']:5.2f}%)  med={rec['med_knz']:5.2f}  "
              f"max={rec['Rmax_knz']:6.2f}  null {rec['null_mean']:5.2f}/"
              f"{rec['null_max']:5.2f} ge={rec['null_ge']}/{n_null}")
        print(f"        PLANT {pl}   floor={rec['floor']}")
        sys.stdout.flush()
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", type=int, nargs="+", default=[823, 1303, 1831, 2251])
    ap.add_argument("--fams", nargs="+", default=["Q", "C", "I", "M"])
    ap.add_argument("--nnull", type=int, default=8)
    ap.add_argument("--seed", type=int, default=20260730)
    ap.add_argument("--out", default="phase_family_scan_v1.json")
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    out = []
    for p in a.primes:
        print(f"p={p}")
        r = run(p, a.fams, a.nnull, rng)
        if r:
            out.append(r)
    json.dump(out, open(a.out, "w"), indent=1)
    print(f"\nwrote {a.out}")


if __name__ == "__main__":
    main()
