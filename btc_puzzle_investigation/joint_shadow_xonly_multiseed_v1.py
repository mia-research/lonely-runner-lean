#!/usr/bin/env python3
"""joint_shadow_xonly_multiseed_v1.py -- item 1: close the flagged, UNBANKED sub-observation.

RESULT_joint_shadow_decompose_v2.md, "Flagged sub-observation (not banked)":
  x-only CHAR runs ~0.01-0.02 BELOW x-only RANDOM at all four primes
  (0.6699<0.6881, 0.6734<0.6749, 0.6633<0.6723, 0.6588<0.6609) -- direction-consistent 4/4, tiny,
  and tested against a SINGLE random seed.  That file says what it needs:
  "needs a multi-seed null to place char in the random distribution."   No follow-up exists.

DEFECT REPAIRED: joint_shadow_decompose_v1.py:184 draws ONE random target, `default_rng(p+1)`.
4/4 direction-consistency against one draw each is 1/16 under a fair coin -- not evidence either way.
Here the char fidelity is ranked against N_SEEDS independent random targets per prime.

Float note (CLAUDE.md): recon_fidelity is float numerics inherited from the module, used ONLY as a
monotone statistic RANKED against a matched null of identically-constructed random targets. The
reported readout is an INTEGER RANK; no float threshold decides anything.

PRE-COMMITTED READOUT (fixed before running):
  rank of char among N_SEEDS random targets, per prime (rank 0 = char below every random draw).
  * char inside the body at every prime            -> SEED NOISE; sub-observation CLOSED.
  * char at/below the 5th percentile at every prime -> effect REAL; promote to a finding needing
                                                       its own prereg (do not read it further here).
  * anything else                                   -> report as-is, promote nothing.
"""
import numpy as np
import joint_shadow_decompose_v1 as J

N_SEEDS = 200

if __name__ == "__main__":
    print("x-only phase-recon fidelity: CHAR vs %d independent RANDOM targets" % N_SEEDS)
    print("=" * 78)
    verdicts = []
    for lo, hi in [(150, 250), (250, 400), (400, 550), (550, 750)]:
        r = J.prime_order_curve(lo, hi)
        if not r:
            continue
        p, n, G = r
        xs, ys = J.group_coords(G, p, n, 0)
        w1 = np.exp(2j * np.pi * 1 * np.arange(1, n) / n)
        sm = J.sep_mask(p)
        char = J.recon_fidelity(xs, ys, p, n, w1, sm)
        rng = np.random.default_rng(20260801 + p)
        nulls = []
        for _ in range(N_SEEDS):
            g = np.exp(2j * np.pi * rng.random(n - 1))
            nulls.append(J.recon_fidelity(xs, ys, p, n, g, sm))
        nulls_sorted = sorted(nulls)
        rank = sum(1 for z in nulls if z < char)
        pct5 = nulls_sorted[N_SEEDS // 20]
        below = char <= pct5
        verdicts.append(below)
        print("p=%4d n=%4d | char=%.4f | random: min=%.4f med=%.4f max=%.4f | "
              "rank %3d/%d | %s"
              % (p, n, char, nulls_sorted[0], nulls_sorted[N_SEEDS // 2], nulls_sorted[-1],
                 rank, N_SEEDS, "<=5th pctile" if below else "in the body"))
    print("=" * 78)
    if all(verdicts) and verdicts:
        print("VERDICT: char at/below the 5th percentile at EVERY prime -> effect is REAL.")
        print("         Promote to a finding; it needs its own pre-registration. Not read further here.")
    elif not any(verdicts):
        print("VERDICT: char sits in the body of the random distribution at every prime.")
        print("         The 4/4 direction-consistency was SEED NOISE. Sub-observation CLOSED,")
        print("         scope: x-only phase-recon fidelity, these 4 primes, %d seeds each." % N_SEEDS)
    else:
        print("VERDICT: mixed across primes -> report as-is, promote nothing.")
