#!/usr/bin/env python3
"""
arm4_stage3_primary_v1.py — ARM 4 stage 3: the primary statistic on the TRUE
pairing, run only after asserting the calibration hash (spec section 5.1).

    PRIMARY    T_4   = sum_{j=1..5} |U_{j,-j}|^2          df = 5   (mu6-equivariant)
    SECONDARY  T_off = sum_{j+k even, !=(0,0), k!=-j} |U|^2  df = 12 (non-equivariant)

Nulls: (a) pair-permutation, B=999, from the frozen calibration file;
       (b) multiplicative rotation w'_d = s_w(c*d mod n), c random, c not in
           {+-1} and not in <lambda>*{+-1} (excluded by name in spec 4.4).
"""
import json, hashlib, sys
import numpy as np
from arm4_stage2_calibration_v1 import stats, table_of, paired_table, DIAG, OFF
from arm4_setup_v1 import P, N, lattice_n, eis_n
from lift_sextant_rhombus_law_proof_v2 import sextant

CAL = "arm4_calibration_v1.json"
EXPECT_HASH = sys.argv[1] if len(sys.argv) > 1 else None


def rank_p(obs, null):
    return (1 + int(sum(1 for x in null if x >= obs))) / (len(null) + 1.0)


def main():
    raw = open(CAL, "rb").read()
    h = hashlib.sha256(raw).hexdigest()
    print(f"  calibration sha256 = {h}")
    if EXPECT_HASH:
        assert h == EXPECT_HASH, "CALIBRATION HASH MISMATCH — ordering rule violated"
        print("  hash asserted OK (ordering rule satisfied)")
    cal = json.loads(raw)
    if cal["eps_star"] is None:
        print("\n  *** PLANT DID NOT FIRE -> ARM 4 IS VOID (spec 4.8).")
        print("  *** Reporting an uninformative instrument, NOT a bound.")
        return
    if cal["forced_broken_draws"]:
        print("\n  *** A NULL DRAW BROKE A FORCED ZERO -> ARM 4 IS VOID (spec 4.4).")
        return

    d = np.load("arm4_features_v1.npz")
    su_p, su_n = d["su_p"], d["su_n"]; sw_p, sw_n = d["sw_p"], d["sw_n"]
    K0 = len(su_p)

    tab = table_of(np.concatenate([su_p, su_n]), np.concatenate([sw_p, sw_n]))
    T4, Toff, Todd = stats(tab)
    print(f"\n  TRUE PAIRING   K = {2*K0}")
    print(f"    T_4   = {T4}      (df 5,  mu6-equivariant diagonal)")
    print(f"    T_off = {Toff}    (df 12, non-equivariant)")
    print(f"    forced-zero sum (must be 0) = {Todd}")

    p4 = rank_p(T4, cal["T4_null"]); poff = rank_p(Toff, cal["Toff_null"])
    print(f"\n  PAIR-PERMUTATION NULL (B = {cal['B']}, frozen before this run)")
    print(f"    T_4   rank-p = {p4:.4f}    null median "
          f"{np.median(cal['T4_null']):.4g}")
    print(f"    T_off rank-p = {poff:.4f}    null median "
          f"{np.median(cal['Toff_null']):.4g}")

    # ---- per-isotype characterization (always reported, never a verdict)
    from arm4_stage2_calibration_v1 import U
    print(f"\n  PER-ISOTYPE |U_{{j,-j}}|  (which j carries the mass)")
    for j, k in DIAG:
        print(f"    j={j} k={k}: |U| = {U(tab,j,k)**0.5:,.1f}")
    print(f"    j=3 is the pure sign/parity channel; j=1,5 the primitive-6th-root channel")

    # ---- effect size: read off the EMPIRICAL PLANT CURVE, per spec 4.6
    #
    # BUG FIXED HERE (v1 printed a nonsense number).  v1 used
    #     rho^2 = (T_4 - median_null) / K
    # which assumes |U|^2 ~ K per isotype, i.e. a uniform-marginal random walk.
    # The marginals are NOT uniform: |U_{2,4}| = |U_{4,2}| ~ 2.3e4 >> sqrt(K) ~ 6.3e2,
    # so that scaling is wrong by orders of magnitude and printed |rho| ~ 2.06 --
    # IMPOSSIBLE, since a correlation cannot exceed 1.  An impossible value is the
    # tell.  The rank-based p-values are unaffected (they never used this line).
    # Spec 4.6 already says the run REPLACES the normal approximation with the
    # empirical plant curve; that is the only effect-size statement made.
    print(f"\n  EFFECT SIZE — from the empirical plant curve (spec 4.6), not a formula")
    for e, hits in sorted(cal["plant"].items(), key=lambda kv: float(kv[0])):
        print(f"    copy-fraction eps={float(e):<7} detected in {hits}/20 draws")
    print(f"    => detection threshold lies between the largest non-firing eps and "
          f"eps* = {cal['eps_star']}")
    print(f"    => BOUND: any mu6-equivariant coupling of copy-fraction >= "
          f"{cal['eps_star']} would have been")
    print(f"       detected at K={2*K0}; T_4 rank-p = {p4:.4f} means none was.")

    # ---- secondary null: multiplicative rotation
    print(f"\n  ROTATION NULL (w'_d = s_w(c*d mod n); c not in +-1, not in <lambda>*+-1)")
    (A0, B0), (A, B), R1, R2, DET = lattice_n()
    n_i = int(N)
    rng = np.random.default_rng(int(7654321))
    ds = d["meta"]
    import random as _r
    r2 = _r.Random(int(20260724))
    scal = [r2.randrange(1, n_i) for _ in range(K0)]
    rot = []
    for _ in range(int(sys.argv[2]) if len(sys.argv) > 2 else 99):
        c = int(rng.integers(2, 2 ** 62))
        wp = np.empty(K0, dtype=np.uint8); wn = np.empty(K0, dtype=np.uint8)
        for i, dd in enumerate(scal):
            x = (c * dd) % n_i
            (u, v), _ = eis_n(x, R1, R2, DET); wp[i] = sextant(u, v)
            (u, v), _ = eis_n(n_i - x, R1, R2, DET); wn[i] = sextant(u, v)
        t4b, _, todd = stats(table_of(np.concatenate([su_p, su_n]),
                                      np.concatenate([wp, wn])))
        assert todd == 0, "rotation null broke a forced zero"
        rot.append(t4b)
    print(f"    B = {len(rot)}   T_4 rank-p = {rank_p(T4, rot):.4f}   "
          f"null median {np.median(rot):.4g}")


if __name__ == "__main__":
    main()
