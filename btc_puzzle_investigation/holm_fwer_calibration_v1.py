#!/usr/bin/env python3
"""PREREG_incomplete_shortscalar_v2 §2·CAL — FWER calibration of the PRIMARY rule.

WHAT IS BEING CALIBRATED
------------------------
v2 §2.2 primary decision: per-law permutation p-values

    p_l = (1 + #{k : G_l(control_k) >= G_l(short)}) / (1 + K)

with G_l = sum_c (o_c - mbar_c)^2 / mbar_c against a LEAVE-ONE-OUT control-ensemble
mean, then Holm step-down over the 5 tests {sextant, norm, flap, C_T, joint} at
family-wise alpha = 0.05.

The structural worry (named in the v1 self-audit): the control ensemble is used
TWICE -- once to form mbar, again as the reference distribution for the rank.
That is the obvious place for an anti-conservative null.  This measures whether
the leave-one-out scheme actually fixes it.

WHAT IS MEASURED
  1. per-law p-value validity: P(p_l <= 0.05) and P(p_l <= 0.01) under H0
  2. realized family-wise error rate of the Holm rule at nominal 0.05
  3. sensitivity to the norm-band cell vector (not recoverable from the record
     files; the test is a RANK test so it should not matter -- this shows it)
  4. sensitivity to K

NOT A SIGNAL PATH.  This is a calibration study of the test procedure, so the
no-float rule's signal-path ban does not apply (same carve-out the v1 self-audit
declared).  The real run computes G_l as fractions.Fraction on integer counts.
"""

import numpy as np
import sys

rng = np.random.default_rng(20260730)

# ---------------------------------------------------------------- cell vectors
# sextant: 6 cells, equidistributed on the complete orbit (v2 sec.0)
P_SEXTANT = np.full(6, 1.0 / 6)

# flap / CM-spine: core : flap+ : flap- = 3/4 : 1/8 : 1/8 (v2 sec.0, Cap Law)
P_FLAP = np.array([0.75, 0.125, 0.125])

# C_T: 9 cells, tensor law C_T ~ C1 (x) C2 with each factor 3/4 : 1/8 : 1/8
P_CT = np.outer(P_FLAP, P_FLAP).ravel()

# T_joint: 16 cells = 4 within-family quantile bands x 4 norm-bands
# (quantile bands are equiprobable by construction)

# norm-band: 4 cells.  Only the first is exactly derivable from the record:
# density 2*pi/sqrt(3) on [0, 3/16]  =>  P(cell 1) = (3/16)*2*pi/sqrt(3).
P_NB_HEAD = (3.0 / 16) * 2 * np.pi / np.sqrt(3)
NORM_VARIANTS = {
    "record-head + even tail": np.array(
        [P_NB_HEAD] + [(1 - P_NB_HEAD) / 3] * 3),
    "record-head + decreasing tail": np.array(
        [P_NB_HEAD, (1 - P_NB_HEAD) * 0.5, (1 - P_NB_HEAD) * 0.3,
         (1 - P_NB_HEAD) * 0.2]),
    "uniform 4-cell": np.full(4, 0.25),
    "adversarial skew (small expected counts)": np.array(
        [0.90, 0.06, 0.03, 0.01]),
}


def perm_pvalue(counts):
    """counts: (K+1, C) integer array.  Row 0 = the sample under test,
    rows 1..K = the control ensemble.  Returns the permutation p-value using a
    LEAVE-ONE-OUT ensemble mean, exactly as v2 sec.2.1 specifies."""
    K = counts.shape[0] - 1
    ctrl = counts[1:]
    tot = ctrl.sum(axis=0)

    # row 0 uses the mean of all K controls
    mbar0 = tot / K
    g0 = np.sum((counts[0] - mbar0) ** 2 / mbar0)

    # each control uses the mean of the OTHER K-1 controls
    mbar = (tot - ctrl) / (K - 1)
    gk = np.sum((ctrl - mbar) ** 2 / mbar, axis=1)

    return (1 + np.count_nonzero(gk >= g0)) / (1 + K)


def holm_any(pvals, alpha=0.05):
    """Holm step-down.  Returns True iff ANY hypothesis is rejected."""
    m = len(pvals)
    sp = np.sort(pvals)
    for i in range(m):
        if sp[i] > alpha / (m - i):
            return i > 0
    return True


def run(reps, K, M_by_law, p_norm, label, seed_off=0):
    """One calibration block.  Everything drawn under H0: the 'short' family is
    an exchangeable draw from the SAME multinomial as the controls."""
    r = np.random.default_rng(20260730 + seed_off)
    laws = [
        ("sextant", P_SEXTANT, M_by_law["sextant"]),
        ("norm",    p_norm,    M_by_law["norm"]),
        ("flap",    P_FLAP,    M_by_law["flap"]),
        ("C_T",     P_CT,      M_by_law["C_T"]),
        ("joint",   np.full(16, 1 / 16), M_by_law["joint"]),
    ]
    hits05 = np.zeros(len(laws))
    hits01 = np.zeros(len(laws))
    fwer = 0

    for _ in range(reps):
        pv = np.empty(len(laws))
        for j, (_nm, p, M) in enumerate(laws):
            counts = r.multinomial(M, p, size=K + 1)
            pv[j] = perm_pvalue(counts)
        hits05 += (pv <= 0.05)
        hits01 += (pv <= 0.01)
        if holm_any(pv, 0.05):
            fwer += 1

    print(f"\n### {label}   (reps={reps}, K={K})")
    print(f"{'law':>10} {'P(p<=.05)':>12} {'P(p<=.01)':>12}")
    for j, (nm, _p, _M) in enumerate(laws):
        print(f"{nm:>10} {hits05[j]/reps:>12.4f} {hits01[j]/reps:>12.4f}")
    se = (0.05 * 0.95 / reps) ** 0.5
    print(f"  Holm FWER @ nominal 0.05 : {fwer/reps:.4f}"
          f"   (MC se {se:.4f}; nominal 0.05)")
    return fwer / reps


if __name__ == "__main__":
    quick = "--quick" in sys.argv

    # sample sizes at the B=1e4 primary rung (v2 sec.5):
    #   beta-triples ~ 0.6*B = 6000   (the flap / C_T sample unit)
    #   distinct x   ~ 1.8*B = 18000  (sextant / norm-band sample)
    M_BIG = {"sextant": 18000, "norm": 18000, "flap": 6000,
             "C_T": 36000, "joint": 18000}
    # a deliberately small-count regime, where rank tests are most fragile
    M_SMALL = {"sextant": 600, "norm": 600, "flap": 200,
               "C_T": 1200, "joint": 600}

    REPS = 2000 if quick else 20000
    K_MAIN = 999

    print("=" * 72)
    print("PRIMARY CALIBRATION  --  per-law + Holm(5) @ family alpha = 0.05")
    print("=" * 72)
    run(REPS, K_MAIN, M_BIG, NORM_VARIANTS["record-head + even tail"],
        "B=1e4 sample sizes, record-head norm-band")

    print("\n" + "=" * 72)
    print("SENSITIVITY 1 -- norm-band cell vector (rank test: should not matter)")
    print("=" * 72)
    for name, pv in NORM_VARIANTS.items():
        run(REPS // 4, K_MAIN, M_BIG, pv, name, seed_off=hash(name) % 1000)

    print("\n" + "=" * 72)
    print("SENSITIVITY 2 -- K")
    print("=" * 72)
    for K in (199, 999, 4999):
        run(REPS // 4, K, M_BIG, NORM_VARIANTS["record-head + even tail"],
            f"K={K}", seed_off=K)

    print("\n" + "=" * 72)
    print("SENSITIVITY 3 -- small-count regime (most fragile for a rank test)")
    print("=" * 72)
    run(REPS // 2, K_MAIN, M_SMALL,
        NORM_VARIANTS["adversarial skew (small expected counts)"],
        "small M + adversarial skew", seed_off=7)
