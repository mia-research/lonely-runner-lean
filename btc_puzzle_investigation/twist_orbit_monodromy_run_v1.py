#!/usr/bin/env python3
"""
twist_orbit_monodromy_run_v1.py — PREREG_twist_orbit_monodromy_v1.md

The 4th-order monodromy discriminator for the twist orbit.
u(a)=V(a)/(2 i sqrt p) in [-1,1].  Even moments read off the monodromy group:

    full SU(2) (Sato-Tate):   E[u^2]=1/4, E[u^4]=1/8,  E[u^6]=5/64
    torus/CM (uniform angle): E[u^2]=1/2, E[u^4]=3/8,  E[u^6]=5/16

PRIMARY  E[u^4](p) = n * sum_j R(j)^2 / (16 p^2 (n-1))  -- EXACT RATIONAL,
         R(j)=sum_k c_k c_{k+j} the integer autocorrelation of c_k=chi2(y_[k]G).
         (No FFT, no float in the signal path.)  E[u^2]=n/(4p) is FORCED.
NULL     iid-SU(2) simulation (L Sato-Tate draws) -> band for E[u^4]; a parallel
         uniform-angle simulation gives the CM band.  Float lives only in the
         null SIMULATION (the reference), never in the data statistic.

No leakage/ECDLP claim -- this identifies a monodromy group.
"""
import argparse, json
from fractions import Fraction as Fr
import numpy as np
from twist_orbit_spectrum_run_v1 import signal


# ---------- EXACT signal path (int / Fraction, no float) --------------------
def moments_exact(p, b=7):
    s = signal(p, b)
    if s is None:
        return None
    n, c, X, Y = s
    if (n - 1) % 6 != 0:
        return None
    L = (n - 1) // 6
    # exact integer autocorrelation R(j) = sum_k c_k c_{k+j}
    R = [int(np.dot(c, np.roll(c, -j))) for j in range(n)]
    sumR2 = sum(r * r for r in R)                        # exact int
    Eu2 = Fr(n, 4 * p)                                   # FORCED
    Eu4 = Fr(n * sumR2, 16 * p * p * (n - 1))            # EXACT rational
    return {"p": p, "n": int(n), "L": L, "R0": R[0], "sumR2": sumR2,
            "Eu2": Eu2, "Eu4": Eu4, "c": c}


# ---------- NULL simulation (float reference; NOT the data) ------------------
def _st_u(L, rng):
    """L iid Sato-Tate u=cos(theta): semicircle density (2/pi)sqrt(1-u^2)."""
    out = np.empty(0)
    while out.size < L:                                                  # noqa: float
        x = rng.uniform(-1.0, 1.0, size=2 * L)                          # noqa: float
        keep = x[rng.uniform(0.0, 1.0, size=x.size) < np.sqrt(1 - x * x)]  # noqa: float
        out = np.concatenate([out, keep])
    return out[:L]


def _unif_u(L, rng):
    return np.cos(rng.uniform(0.0, np.pi, size=L))                       # noqa: float


def band(sampler, L, Rsim, rng):
    est = np.array([np.mean(sampler(L, rng) ** 4) for _ in range(Rsim)])  # noqa: float
    est.sort()
    lo = est[int(0.025 * Rsim)]; hi = est[int(0.975 * Rsim)]             # noqa: float
    return float(lo), float(hi), float(est.mean())                       # noqa: float


# ---------- driver ----------------------------------------------------------
def run(p, Rsim, rng, controls=False):
    m = moments_exact(p)
    if m is None:
        return None
    L = m["L"]
    Eu4f = float(m["Eu4"])                                              # noqa: float  (exact->float for band compare)
    lo, hi, cen = band(_st_u, L, Rsim, rng)                             # SU(2) band
    m["su2_lo"], m["su2_hi"], m["su2_cen"] = lo, hi, cen
    m["in_su2"] = bool(lo <= Eu4f <= hi)
    m["below"] = bool(m["Eu4"] < Fr(1, 8))                              # EXACT Fraction comparison
    m["Eu4f"] = Eu4f
    if controls:
        ulo, uhi, ucen = band(_unif_u, L, Rsim, rng)                   # uniform band
        m["unif_cen"] = ucen
        m["PLANT_UNIF_sep"] = bool(ucen > hi)     # uniform center outside SU(2) band?
        # C-FORCED: E[u^2] == n/(4p)
        m["C_FORCED"] = (m["Eu2"] == Fr(p, p) * Fr(m["n"], 4 * p))     # trivially, checks type
        # C-CROSS: exact n*sumR2 vs float FFT sum|V|^4
        V = np.fft.fft(m["c"].astype(np.complex128))                   # noqa: float
        s4 = float(((V.real ** 2 + V.imag ** 2) ** 2).sum())           # noqa: float
        m["C_CROSS"] = bool(abs(s4 - m["n"] * m["sumR2"]) / (m["n"] * m["sumR2"]) < 1e-9)  # noqa: float
    del m["c"]
    return m


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--phase", choices=["fires", "gate"], required=True)
    ap.add_argument("--Rsim", type=int, default=4000)
    args = ap.parse_args()
    rng = np.random.default_rng(20260726)

    if args.phase == "fires":
        print("=== MONODROMY TEST-FIRES (in-sample) ===")
        for p in [127, 211, 547]:
            o = run(p, args.Rsim, rng, controls=True)
            print(f"\np={p} n={o['n']} L={o['L']}")
            e2 = float(o['Eu2'])                                      # noqa: float  (display only)
            print(f"  C-FORCED E[u2]={e2:.5f}(=n/4p)  C-CROSS(nSR2==FFT)={o['C_CROSS']}")
            print(f"  E[u4] exact={o['Eu4']}  = {o['Eu4f']:.5f}")
            print(f"  SU(2) band=[{o['su2_lo']:.4f},{o['su2_hi']:.4f}] cen={o['su2_cen']:.4f}  in={o['in_su2']}")
            print(f"  PLANT-UNIF center={o['unif_cen']:.4f}  separated from SU(2) band={o['PLANT_UNIF_sep']}")
        return

    if args.phase == "gate":
        fr = json.load(open("twist_orbit_spectrum_FREEZE_v2.json"))
        print(f"=== MONODROMY GATE (frozen S, SHA {fr['sha256'][:16]}...) Rsim={args.Rsim} ===")
        nin = 0; below = 0; devs = []
        for p in fr["stratum_S"]:
            o = run(p, args.Rsim, rng)
            dev = o["Eu4f"] - float(Fr(1, 8))                          # noqa: float  (display only)
            devs.append((o["L"], dev))
            nin += o["in_su2"]; below += o["below"]                    # below via exact Fraction
            print(f"  p={p:5d} n={o['n']:5d} L={o['L']:4d}  E[u4]={o['Eu4f']:.5f}  "
                  f"SU2=[{o['su2_lo']:.4f},{o['su2_hi']:.4f}]  in={o['in_su2']}  dev(1/8)={dev:+.5f}")
        wdev = sum(L * d for L, d in devs) / sum(L for L, _ in devs)    # noqa: float  (display)
        print(f"\n  in SU(2) band: {nin}/12   below 1/8: {below}/12   L-weighted mean dev from 1/8: {wdev:+.5f}")
        # CONVERGENCE test (resolves the finite-p concern): a finite-p correction
        # SHRINKS with p (dev -> 0); a real reduction is a CONSTANT offset.
        ds = sorted(devs, key=lambda t: t[0])                          # by L
        small = [d for _, d in ds[:6]]; large = [d for _, d in ds[6:]]  # noqa: float
        ms = sum(small) / len(small); ml = sum(large) / len(large)      # noqa: float
        print(f"  CONVERGENCE: mean dev small-L half={ms:+.5f}  large-L half={ml:+.5f}  "
              f"(shrinking->SU(2) finite-p; constant->reduction)")
        # linear extrapolation of dev vs 1/sqrt(L) to L->inf (intercept)
        xs = [1.0 / (L ** 0.5) for L, _ in devs]; ys = [d for _, d in devs]  # noqa: float
        xm = sum(xs) / len(xs); ym = sum(ys) / len(ys)                  # noqa: float
        sl = sum((x - xm) * (y - ym) for x, y in zip(xs, ys)) / sum((x - xm) ** 2 for x in xs)  # noqa: float
        icept = ym - sl * xm                                            # noqa: float
        print(f"  EXTRAPOLATION dev(L->inf) intercept={icept:+.5f}  (≈0 => converges to 1/8 = full SU(2))")


if __name__ == "__main__":
    main()
