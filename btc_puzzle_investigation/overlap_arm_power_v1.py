#!/usr/bin/env python3
"""
overlap_arm_power_v1.py -- PLANTED-POSITIVE control for the OVERLAP arm of lift_band_spectral_v1.py.

The overlap arm (final block of `lift_band_spectral_v1.run_curve`) correlates each curve readout's
low-frequency power spectrum against the band targets `derr` / `k_den`, ranks the Pearson rho against
a permutation of the curve vector, and reports |z|.  It ships a matched NULL (`shuffle_floor` /
permutation of `cvec`) but NO planted positive.  Per the repo standard recorded in memory
`btc_puzzle_pubkey_relations_controlled_2026_07_18` ("audit OLD nulls for a firing control before
trusting"), a null without a firing control is uninformative.

This file supplies the missing control and measures the arm's DETECTION FLOOR:

  plant(f) = a synthetic curve readout carrying amplitude fraction f of a band target's structure,
             mixed with a variance-matched white component:
                 plant = f * (target)  +  (1-f) * (white)
             realised in EXACT INTEGER arithmetic (see DISCIPLINE).

  sweep f downward, record the smallest f at which the arm's own |z| > 3 threshold fires,
  at a stated detection RATE over independent plant draws  (power, not a single lucky draw).

Two plant families, because "white" can mean two different things:

  PLANT A (self-noise):  noise = a random permutation of the target itself.
        Exactly variance-matched and exactly value-multiset-matched by construction, zero float in
        the mixture.  f=0 degenerates to the arm's own null, so the f=0 row IS the false-positive
        control-of-the-control.

  PLANT B (real-readout noise): noise = an ACTUAL curve readout (eis_u, eis_v, norm_s, flap_eps,
        sextant, sign_xy) from the same band.  This is the faithful counterfactual: "if this real
        readout had carried fraction f of k_den, would the arm have seen it?"  f=0 reproduces the
        arm's published rows exactly.

BRIDGE TO THE OBSERVED NULL (the point of the exercise).  `RESULT_lrc_null_typing_transfer_v1.md`
§2.3 notes every real curve readout sits at low-frequency excess ~1.0x (the white floor), so the
overlap correlation takes noise as one of its two inputs and its outcome may have been fixed
upstream.  So for every f this file ALSO reports the planted sequence's own low-frequency excess --
the same observable the arm already prints for real readouts.  That converts the detection floor from
an abstract f into a statement in the units the real readouts are measured in.

DISCIPLINE (btc_puzzle_investigation/CLAUDE.md -- numerical integrity):
 * signal path exact int, and SPLIT OUT into `overlap_plant_exact_v1.py` so it can be guard-checked
   on its own (`bash check_no_float.sh overlap_plant_exact_v1.py` -> OK).  Targets, readouts and the
   planted mixture are Python INTEGERS; scale matching uses isqrt + `Fraction.limit_denominator`
   (exact bounded-denominator rational), never a float ratio.  That module's `selftest()` runs first
   in `main()` and Fraction-verifies every plant configuration before any statistic is reported.
 * every planted sequence is asserted < 2^52 in absolute value before the FFT, so the float FFT
   loses no bits of the integer signal (the same guarantee the parent file relies on for toy values).
 * float appears ONLY as the monotone statistic (power spectrum -> Pearson rho -> z), ranked against
   the SAME matched permutation null the parent arm uses.  No float threshold touches the data.
 * the statistic function is imported/reproduced verbatim from the parent arm -- the control tests
   the arm as written, not a re-implementation of it.

OUTPUT: a detection floor reported as a SCOPED BOUND WITH POWER (this band, this L, this kmax, this
threshold, this many draws), never as a closure.
"""
import sys

import numpy as np

from lift_band_spectral_v1 import power_spectrum, low_freq_mass, shuffle_floor
# EXACT-INT signal path lives in its own module so it can be guard-checked on its own:
#     bash check_no_float.sh overlap_plant_exact_v1.py   ->  OK   (verified)
# Nothing below re-implements it; this file is the statistic layer only.
from overlap_plant_exact_v1 import build_band, plant, FLOAT_EXACT_BOUND, selftest

Z_THRESHOLD = 3.0                    # the arm's own firing threshold
NULL_REPS = 200                      # the arm's own permutation-null size


# ---------------------------------------------------------------------------
# the arm's statistic, reproduced verbatim from lift_band_spectral_v1.run_curve
# ---------------------------------------------------------------------------
def overlap_z(dref, cvec, rng, reps=NULL_REPS):
    """Pearson of two mean-removed low-freq power vectors, z-ranked against permutations of cvec."""
    rho = float(np.dot(dref, cvec)) / (float(np.linalg.norm(dref) * np.linalg.norm(cvec)) + 1e-18)
    nulls = []
    for _ in range(reps):
        cs = rng.permutation(cvec)
        nulls.append(float(np.dot(dref, cs)) /
                     (float(np.linalg.norm(dref) * np.linalg.norm(cs)) + 1e-18))
    z = (rho - np.mean(nulls)) / (np.std(nulls) + 1e-12)
    return rho, float(z)


def lf_vector(seq_int, lfidx):
    """low-frequency power-spectrum vector of an INTEGER sequence, mean-removed (the arm's cvec)."""
    arr = np.asarray(seq_int, dtype=object)
    mx = max(int(abs(x)) for x in arr)
    assert mx < FLOAT_EXACT_BOUND, "planted integer %d exceeds 2^52; float FFT would lose bits" % mx
    P = power_spectrum(np.array([float(x) for x in arr]))
    v = P[lfidx]
    return P, v - v.mean()


def excess(P, seq_int, kmax, seed):
    """low-freq excess of a spectrum vs the shuffle floor of the SAME multiset (the arm's readout).

    Identical statistic to the `lf_excess` column lift_band_spectral_v1 prints for real readouts, so
    the planted sequences and the real ones are on one scale.
    """
    F = shuffle_floor([float(x) for x in seq_int], reps=20, seed=seed)
    return low_freq_mass(P, kmax) / (low_freq_mass(F, kmax) + 1e-18)


# ---------------------------------------------------------------------------
# the sweep
# ---------------------------------------------------------------------------
F_GRID =[1.0, 0.7, 0.5, 0.35, 0.25, 0.18, 0.12, 0.09, 0.06, 0.04,
          0.03, 0.02, 0.015, 0.01, 0.007, 0.005, 0.003, 0.002, 0.001, 0.0]
B_DEN = 1024
N_DRAWS_A = 40          # independent plant draws per f (PLANT A)


def run_curve_power(lo, hi, bexp, M, kmax=16):
    got = build_band(lo, hi, bexp, M)
    if not got:
        print("  (no usable prime-order curve in [%d,%d])" % (lo, hi)); return None
    p, n, A, L, targets, readouts = got
    lfidx = list(range(1, kmax + 1)) + list(range(L - kmax, L))

    print("\n" + "=" * 96)
    print(" curve p=%d n=%d  band A=%d L=%d  Farey cap M=%d  kmax=%d  |lf vector|=%d"
          % (p, n, A, L, M, kmax, len(lfidx)))
    print("=" * 96)

    out = {}
    for tname, tseq in targets.items():
        Pt, dref = lf_vector(tseq, lfidx)
        t_exc = excess(Pt, tseq, kmax, seed=11)
        print("\n TARGET %s   low-freq excess of the target itself = %.1fx" % (tname, t_exc))

        # ---------------- PLANT A : noise = permutation of the target ----------------
        print("   PLANT A  (noise = permutation of the target; exactly variance- and multiset-matched)")
        print("     %-7s  %-9s  %-9s  %-8s  %s" %
              ("f", "det.rate", "med |z|", "med rho", "planted lf-excess (med)"))
        rowsA = []
        for f in F_GRID:
            a = int(round(f * B_DEN))
            zs = []; rhos = []; excs = []
            for k in range(N_DRAWS_A):
                rp = np.random.default_rng(1000 + k)
                noise = list(rp.permutation(np.array(tseq, dtype=np.int64)))
                mix = plant(tseq, noise, a, B_DEN)
                Pm, cvec = lf_vector(mix, lfidx)
                rng = np.random.default_rng(50_000 + k)
                rho, z = overlap_z(dref, cvec, rng)
                zs.append(abs(z)); rhos.append(rho)
                if k < 6:                       # excess is expensive; 6 draws is enough for a median
                    excs.append(excess(Pm, mix, kmax, seed=7))
            rate = float(np.mean([1.0 if v > Z_THRESHOLD else 0.0 for v in zs]))
            rowsA.append((f, rate, float(np.median(zs)), float(np.median(rhos)),
                          float(np.median(excs))))
            print("     %-7.3f  %-9.2f  %-9.1f  %-8.3f  %.2fx" % rowsA[-1])

        # ---------------- PLANT B : noise = a REAL curve readout ----------------
        print("   PLANT B  (noise = a real curve readout; f=0 row reproduces the published arm)")
        print("     %-7s  %-9s  %-9s  %-8s  %s" %
              ("f", "det.rate", "med |z|", "med rho", "planted lf-excess (med)"))
        rowsB = []
        for f in F_GRID:
            a = int(round(f * B_DEN))
            zs = []; rhos = []; excs = []
            for j, (rname, rseq) in enumerate(readouts.items()):
                mix = plant(tseq, rseq, a, B_DEN)
                Pm, cvec = lf_vector(mix, lfidx)
                rng = np.random.default_rng(90_000 + j)
                rho, z = overlap_z(dref, cvec, rng)
                zs.append(abs(z)); rhos.append(rho)
                excs.append(excess(Pm, mix, kmax, seed=9))
            rate = float(np.mean([1.0 if v > Z_THRESHOLD else 0.0 for v in zs]))
            rowsB.append((f, rate, float(np.median(zs)), float(np.median(rhos)),
                          float(np.median(excs))))
            print("     %-7.3f  %-9.2f  %-9.1f  %-8.3f  %.2fx" % rowsB[-1])

        out[tname] = {'target_excess': t_exc, 'A': rowsA, 'B': rowsB}
    return p, n, L, out


def calibrate_threshold(lo, hi, bexp, M, kmax=16, ndraws=400):
    """Empirical SIZE of the arm's |z|>3 threshold.

    The arm's z is a permutation rank over a 32-element low-frequency vector, not a gaussian
    z-score.  Its true false-positive rate at |z|>3 is an empirical quantity, not 0.0027.  Measure
    it directly with `ndraws` independent f=0 plants (= structure-free curve readouts with the
    target's own value multiset).
    """
    got = build_band(lo, hi, bexp, M)
    if not got:
        return None
    p, n, A, L, targets, readouts = got
    lfidx = list(range(1, kmax + 1)) + list(range(L - kmax, L))
    rows = []
    for tname, tseq in targets.items():
        _, dref = lf_vector(tseq, lfidx)
        zs = []
        for k in range(ndraws):
            rp = np.random.default_rng(700_000 + k)
            noise = list(rp.permutation(np.array(tseq, dtype=np.int64)))
            _, cvec = lf_vector(noise, lfidx)
            rng = np.random.default_rng(800_000 + k)
            _, z = overlap_z(dref, cvec, rng)
            zs.append(abs(z))
        zs = np.array(zs)
        hits = int((zs > Z_THRESHOLD).sum())
        rows.append((L, tname, ndraws, hits, hits / ndraws,
                     float(np.quantile(zs, 0.95)), float(np.quantile(zs, 0.99)), float(zs.max())))
    return rows


def floor_at(rows, rate):
    """smallest f in the sweep whose detection rate >= `rate`, given the rate is monotone-ish."""
    ok = [r for r in rows if r[1] >= rate]
    return min(r[0] for r in ok) if ok else None


def main():
    print("=" * 96)
    print("EXACT-PATH SELFTEST (overlap_plant_exact_v1) -- run before any statistic is reported")
    print("=" * 96)
    selftest()
    print("=" * 96)
    print("OVERLAP ARM -- PLANTED-POSITIVE CONTROL  (missing firing control for lift_band_spectral_v1)")
    print("threshold = the arm's own |z| > %.1f ; null = the arm's own %d-permutation rank"
          % (Z_THRESHOLD, NULL_REPS))
    print("=" * 96)

    results = []
    for lo, hi, bexp, M in [(2100, 4200, 11, 32),
                            (8200, 16400, 13, 48),
                            (33000, 66000, 15, 64)]:
        got = run_curve_power(lo, hi, bexp, M, kmax=16)
        if got:
            results.append(got)

    print("\n" + "=" * 96)
    print("DETECTION FLOOR  (smallest planted amplitude fraction f reaching the stated rate)")
    print("=" * 96)
    print(" %-10s %-7s %-6s %-24s %-24s" %
          ("curve L", "target", "plant", "f_min @ rate>=0.50", "f_min @ rate>=0.95"))
    for p, n, L, out in results:
        for tname, d in out.items():
            for fam in ('A', 'B'):
                f50 = floor_at(d[fam], 0.50)
                f95 = floor_at(d[fam], 0.95)
                print(" %-10d %-7s %-6s %-24s %-24s" %
                      (L, tname, fam,
                       "%.4f" % f50 if f50 is not None else "never fires",
                       "%.4f" % f95 if f95 is not None else "never fires"))

    print("\n false-positive check (f = 0 row = the arm's own null): rates below should be ~0")
    for p, n, L, out in results:
        for tname, d in out.items():
            for fam in ('A', 'B'):
                r0 = [r for r in d[fam] if r[0] == 0.0][0]
                print("   L=%-6d %-6s plant %s  f=0 detection rate = %.2f   med|z| = %.2f"
                      % (L, tname, fam, r0[1], r0[2]))

    print("\n" + "=" * 96)
    print("THRESHOLD CALIBRATION -- empirical SIZE of the arm's |z| > %.1f rule" % Z_THRESHOLD)
    print("(the arm's z is a 32-element permutation rank, NOT a gaussian; nominal 0.0027 does not apply)")
    print("=" * 96)
    print(" %-8s %-7s %-8s %-6s %-10s %-8s %-8s %-8s" %
          ("L", "target", "draws", "hits", "FP rate", "q95 |z|", "q99 |z|", "max |z|"))
    for lo, hi, bexp, M in [(2100, 4200, 11, 32),
                            (8200, 16400, 13, 48),
                            (33000, 66000, 15, 64)]:
        rows = calibrate_threshold(lo, hi, bexp, M, kmax=16, ndraws=400)
        if not rows:
            continue
        for L, tname, nd, hits, fp, q95, q99, mx in rows:
            print(" %-8d %-7s %-8d %-6d %-10.4f %-8.2f %-8.2f %-8.2f"
                  % (L, tname, nd, hits, fp, q95, q99, mx))


if __name__ == '__main__':
    sys.exit(main())
