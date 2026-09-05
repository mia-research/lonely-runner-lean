#!/usr/bin/env python3
"""
curve_alteration_sweep_v1.py

"Curve alterations" (user 2026-07-13): the shadow may be invisible on secp256k1
(b=7) but visible if we CHANGE THE GEOMETRY -- move the carrier and watch the
shadow move. The a=0 group law is b-agnostic, so for the SAME scalar set {d_i} we
compute P_i=[d_i]G_b on E_b: y^2=x^3+b for a grid of b, over the SAME field F_p
(so the Eisenstein/CM lift + sextic characters are the same instrument each time),
and ask:
  (1) MARGINAL: does the lift-sextant / chi6 distribution of the point set depend
      on b?  (a geometry signature)
  (2) LEAK: does MI(point-stat ; d mod 6 / mid-bit) light up for ANY b (incl 7)?
      -- i.e. is there a curve where the construction leaks the scalar?
  (3) OUTLIER: is b=7 (secp, the unique prime-order j=0 twist) special vs the field?
  (4) INTEGER RESONANCE: fix one d, sweep b, watch X(b) -- any structure/period?

Curves grouped by chi6(b) (the six j=0 sextic-twist classes). Plant control fires.
Exact integers in the signal path (CLAUDE.md).
"""
import numpy as np
from ecc_secp256k1 import scalar_mul, P as p
from eisenstein_lift_sextant_exact_v1 import lift_sextant
from angular_interference_scaling_v1 import chi6, conditional, loglog_slope

NSC = 1500       # scalars per curve
e6 = (p - 1) // 6

def find_base(b):
    """smallest x>=1 with a point on y^2=x^3+b; y via p=3 mod4 sqrt."""
    for x in range(1, 200000):
        rhs = (pow(x, 3, p) + b) % p
        if rhs == 0:
            continue
        if pow(rhs, (p - 1) // 2, p) != 1:
            continue
        return (x, pow(rhs, (p + 1) // 4, p))
    return None

def load_scalars():
    z = np.load("constructed_keys_fullrange_v1.npz", allow_pickle=True)
    mask = np.array([int(v) == 256 for v in z["N"]])
    ds = [int(v) for v in z["d"][mask]][:NSC]
    return ds

def stats_for(ds, base):
    sxt = []; c6 = []; xm7 = []; xt3 = []; xs = []
    for d in ds:
        X, Y = scalar_mul(d, base=base)
        sxt.append(lift_sextant(X)); c6.append(chi6(X) or 0)
        xm7.append(X % 7); xt3.append(X >> (X.bit_length() - 3) if X.bit_length() >= 3 else 0)
        xs.append(X)
    return dict(sextant=np.array(sxt), chi6=np.array(c6),
                Xmod7=np.array(xm7), Xtop3=np.array(xt3)), xs

def main():
    ds = load_scalars()
    d6 = np.array([d % 6 for d in ds]); bmid = np.array([(d >> (d.bit_length()//2)) & 1 for d in ds])
    targets = {"d%6": d6, "bit_mid": bmid}
    bgrid = [1, 2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 41, 53, 71, 97, 127]
    Ms = [500, 1500]
    rng = np.random.default_rng(11)

    print(f"CURVE-ALTERATION SWEEP  ({len(ds)} scalars/curve, {len(bgrid)} curves)")
    print(f"{'b':>4} {'chi6(b)':>7} {'sextant-hist (6)':>34} {'chi2_sxt':>9} "
          f"{'maxZ(stat;d)':>12} {'which':>16}")
    summary = []
    for b in bgrid:
        base = find_base(b)
        S, xs = stats_for(ds, base)
        hist = np.bincount(S["sextant"], minlength=6)
        exp = len(ds) / 6                                   # noqa: float (report)
        chi2 = float(((hist - exp) ** 2 / exp).sum())       # noqa: float (report)
        # leak scan: max |z| over (stat,target)
        best = (0.0, "")                          # noqa: float (z tracker init)
        for sn, sv in S.items():
            for tn, tv in targets.items():
                res = conditional(sv, tv, Ms, 150, rng)
                z = res[-1][2]
                if abs(z) > abs(best[0]):
                    best = (z, f"{sn}~{tn}")
        print(f"{b:>4} {chi6(b):>7} {str(hist.tolist()):>34} {chi2:>9.0f} "
              f"{best[0]:>12.2f} {best[1]:>16}")
        summary.append((b, chi2, best[0]))

    # PLANT control: a leaked stat must fire under the same detector
    leaked = d6.copy()
    resp = conditional(leaked, d6, Ms, 150, rng)
    print(f"\n[PLANT] leaked(d%6) vs d%6:  z={resp[-1][2]:.1f}  I_c={resp[-1][1]:.3f}  (must fire)")

    # (3) is b=7 an outlier in geometry signature or leak?
    chi2s = [s[1] for s in summary]; z7 = [s for s in summary if s[0] == 7][0]
    print(f"\n(3) b=7: sextant-chi2={z7[1]:.0f} (field range {min(chi2s):.0f}-{max(chi2s):.0f}); "
          f"leak-z={z7[2]:.2f}. secp {'OUTLIER' if z7[1]>max(c for c in chi2s if c!=z7[1])+1 else 'typical'} vs other b.")

    # (4) integer resonance: fix one d, sweep b densely, look at X(b) low bits
    d0 = ds[0]
    bb = list(range(1, 129))
    seq = []
    for b in bb:
        base = find_base(b)
        X, _ = scalar_mul(d0, base=base)
        seq.append(X % 256)     # low byte
    arr = np.array(seq, dtype=float)                       # noqa: float (report DFT)
    sp = np.abs(np.fft.rfft(arr - arr.mean()))             # noqa: float (report DFT)
    kpk = int(np.argmax(sp[1:]) + 1)
    print(f"\n(4) fixed d, sweep b=1..128, X%256 sequence: DFT peak at k={kpk} "
          f"mag={sp[kpk]:.0f} vs median={np.median(sp[1:]):.0f} "
          f"(ratio {sp[kpk]/ (np.median(sp[1:])+1e-9):.1f}; >~5 = resonance)")  # noqa: float (report DFT ratio)

if __name__ == "__main__":
    main()
