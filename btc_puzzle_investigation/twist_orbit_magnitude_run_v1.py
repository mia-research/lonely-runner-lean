#!/usr/bin/env python3
"""
twist_orbit_magnitude_run_v1.py — the MAGNITUDE channel (companion to the signed
channel of twist_orbit_spectrum_run_v1.py).

The signed test (odd chars on V) was null; the forced-landscape sweep
(RESULT_twist_orbit_forced_landscape_v1.md) showed the 2-pt additive autocorr and
the 3-pt multiplicative bispectrum are FORCED, leaving ONE free 2nd-order object:

    the arrangement of the ENERGY |V(a)|^2 over Q = (Z/n)^* / mu6.

|V(a)|^2 is mu6-invariant (magnitude), so it is a well-defined function on the
(n-1)/6 classes; its spectrum lives on the EVEN, mu3-trivial characters (j = 0
mod 6).  DC (j=0) is the forced Parseval constant n(n-1) and is EXCLUDED.

STATISTIC   Tmag(p) = max_{j = 0 mod 6, j != 0} |Ehat(chi_j)|^2 .
NULL        permute the L class-energies (destroys arrangement, preserves the
            exact energy multiset = the magnitude marginal the record measured).

Exact signal path reused from twist_orbit_spectrum_run_v1 (Legendre + orbit);
float only in the FFT statistic, ranked against the permutation null.  No
leakage/ECDLP claim.
"""
import argparse, hashlib, json
import numpy as np
from twist_orbit_spectrum_run_v1 import signal, mult_index, Vfull, stratum


def class_energy(V, powg, L):
    """E_c = |V(g^c)|^2 for c=0..L-1 (mu6-invariant => one energy per class)."""
    E = V.real ** 2 + V.imag ** 2                         # noqa: float
    return E[powg[:L]]


def Tmag(Ecls, L):
    """max over even mu3-trivial chars (j=0 mod6, j!=0) of |FFT_{6L}(tile)|^2."""
    full = np.tile(Ecls, 6)                               # mu6-invariant extension
    Eh = np.fft.fft(full)                                 # noqa: float
    j = np.arange(6 * L)
    adm = (j % 6 == 0) & (j != 0)                         # even mu3-trivial, non-DC
    power = Eh.real ** 2 + Eh.imag ** 2
    p_adm = power[adm]
    jstar = j[adm][int(np.argmax(p_adm))]
    return float(p_adm.max()), int(jstar)                 # noqa: float


def perm_p(Ecls, L, Tdat, R, rng):
    ge = 1
    for _ in range(R):
        Ts, _ = Tmag(Ecls[rng.permutation(L)], L)
        if Ts >= Tdat:
            ge += 1
    return ge, R + 1


def run(p, b, R, rng, controls=False):
    s = signal(p, b)
    if s is None:
        return None
    n, c, X, Y = s
    if (n - 1) % 6 != 0:
        return None
    L = (n - 1) // 6
    g, powg = mult_index(n)
    V = Vfull(n, c)
    Ecls = class_energy(V, powg, L)
    Tdat, jstar = Tmag(Ecls, L)
    ge, tot = perm_p(Ecls, L, Tdat, R, rng)
    out = {"p": p, "n": int(n), "L": L, "T": Tdat, "jstar": jstar,
           "pnum": ge, "pden": tot}
    if controls:
        # C-FORCED: DC = 6 * sum(Ecls) = sum_a |V(a)|^2 = n(n-1)  (Parseval)
        out["C_PARSEVAL"] = abs(6 * float(Ecls.sum()) - n * (n - 1)) < 1e-6   # noqa: float
        Ts = np.sort([Tmag(Ecls[rng.permutation(L)], L)[0] for _ in range(400)])  # noqa: float
        p95 = float(Ts[int(0.95 * len(Ts))])              # noqa: float
        out["p95"] = p95
        # PLANT-POS: an even admissible char (class-frequency t0=1 -> j=6), empirical scale
        base = float(Ecls.mean())                         # noqa: float
        amp = float(np.abs(Ecls - base).mean())           # noqa: float
        s2 = np.arange(L)
        tone = base + 3 * amp * np.cos(2 * np.pi * s2 / L)  # noqa: float
        Tp, jp = Tmag(tone, L)
        out["PLANT_POS_T"] = float(Tp); out["PLANT_POS_j"] = int(jp)   # noqa: float
        out["PLANT_POS_fires"] = bool(Tp > 3 * p95)       # noqa: float
        Tn, _ = Tmag(Ecls[rng.permutation(L)], L)
        out["PLANT_NEG_inband"] = bool(Tn <= p95)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--phase", choices=["fires", "gate"], required=True)
    ap.add_argument("-R", type=int, default=3000)
    args = ap.parse_args()
    rng = np.random.default_rng(20260726)

    if args.phase == "fires":
        print("=== MAGNITUDE-CHANNEL TEST-FIRES (in-sample instrument validation) ===")
        for p in [127, 163, 211]:
            o = run(p, 7, R=1500, rng=rng, controls=True)
            ratio = o['PLANT_POS_T'] / o['p95']           # noqa: float  (display)
            print(f"\np={p} n={o['n']} L={o['L']}")
            print(f"  C-PARSEVAL (DC=n(n-1)): {o['C_PARSEVAL']}")
            print(f"  T={o['T']:.3e} jstar={o['jstar']} pval={o['pnum']}/{o['pden']} p95={o['p95']:.3e}")
            print(f"  PLANT-POS T={o['PLANT_POS_T']:.2e} j={o['PLANT_POS_j']} "
                  f"fires={o['PLANT_POS_fires']} [{ratio:.1f}x]")
            print(f"  PLANT-NEG in-band={o['PLANT_NEG_inband']}")
        return

    if args.phase == "gate":
        fr = json.load(open("twist_orbit_spectrum_FREEZE_v2.json"))
        print(f"=== MAGNITUDE GATE (frozen S, SHA {fr['sha256'][:16]}...) R={fr['R']} ===")
        for p in fr["stratum_S"]:
            o = run(p, 7, R=fr["R"], rng=rng)
            print(f"  p={p:5d} n={o['n']:5d} L={o['L']:4d}  Tmag={o['T']:.4e}  "
                  f"jstar={o['jstar']:4d}  pval={o['pnum']:4d}/{o['pden']}")


if __name__ == "__main__":
    main()
