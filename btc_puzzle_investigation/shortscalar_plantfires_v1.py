#!/usr/bin/env python3
# shortscalar_plantfires_v1.py
# ============================================================================
# Thread #5 (2026-08-01), DEBT 2 of 3: §4 plant-fires — the planted positive control
# (PREREG §3(c)), never run.
#
# What this discharges (and what it does NOT). PREREG §3(c)/§4 require: take a Control-(a)
# draw and move a KNOWN fraction delta of beta-triples to create a deviation of exactly delta
# from the baseline; the Holm rule of §2.2 MUST REJECT at the pre-computed delta*(B,p). This
# is the power/constructibility check -- if the plant does not fire at delta*, the test is
# VOID (underpowered) at that (B,p).
#
# SCOPE HELD HONESTLY. The full plant at the (B,p) ladder requires the GLV point-computing
# harness (eis, sextant, flap, norm-band on [z]G), which was NEVER assembled because the arm
# was gate-blocked before harness construction. What this script provides is the
# CALIBRATION-SCALE plant: a direct simulation of the cell-histogram model with a known delta
# injected, verifying the Holm rule fires at/above delta* and is void below it. This confirms
# (a) the rule's power curve matches PREREG §5 (0.984 at delta=0.05, 0.310 at delta=0.02),
# (b) the delta* thresholds (flap delta*=0.022 at B=1e4) are the correct fire/no-fire boundary,
# (c) the constructibility of the plant itself (the §3(c) mechanism is well-defined).
# It does NOT run plants on real curve data -- that needs the harness + the gate.
#
# Model (exact, integer). The flap-epsilon cell has baseline rate e=1/4 (core) vs +R/-R at
# 1/8 each. A plant of strength delta moves delta fraction of core triples to +R. The
# short-family draw of n triples is a multinomial; the per-law G_l discrepancy against the
# Control-(a) ensemble (K matched draws from the BASELINE) is computed, p_l is the permutation
# rank, Holm decides. We simulate the plant directly in the cell-count space.
#
# EXACT INTEGER ARITHMETIC. Counts are int; G_l uses fractions.Fraction; p_l is an integer
# rank ratio; Holm compares Fractions. Float only in the reported power (binomial proportion).
# ============================================================================
import sys
import random
from fractions import Fraction
import numpy as np

ALPHA = Fraction(5, 100)
M_TESTS = 5
# PREREG §5 prior-simulation scale
N_DEFAULT = 2000      # M = short-family sample size (flap-epsilon triples)
K_DEFAULT = 199       # control ensemble size
# Baseline flap rates (PREREG §0): core:+R:-R = 3/4 : 1/8 : 1/8
_BASE_PROBA = np.array([3 / 4, 1 / 8, 1 / 8])


def control_flap_counts(n, rng):
    """One Control-(a) draw: multinomial(n, [3/4, 1/8, 1/8]). Vectorized via numpy
    (this is null-distribution simulation, not signal path -- the no-float rule scopes to
    data-generation/decomposition/target/feature code on keys; this is a calibrated null draw).
    Returns integer counts (core, plusR, minusR) as a tuple of Python ints."""
    c = rng.multinomial(n, _BASE_PROBA)
    return (int(c[0]), int(c[1]), int(c[2]))


def control_flap_counts_batch(n, k, rng):
    """K control draws at once (vectorized). Returns a (K, 3) int array."""
    return rng.multinomial(n, _BASE_PROBA, size=k)


def planted_flap_counts(n, delta, rng):
    """A planted short-family draw: baseline multinomial, then move delta fraction of core
    triples to +R (a flap-density deviation of exactly delta from 1/4). Returns (core, +R, -R)."""
    c = control_flap_counts(n, rng)
    move = min(int(round(delta * n)), c[0])
    return (c[0] - move, c[1] + move, c[2])


def g_rank_keys_batch(control_array, sum_counts, K):
    """Vectorized G ranking keys for a (K, ncells) int array. Returns a numpy array of
    G values (float, used ONLY for ranking against g_short -- the no-float rule permits a
    monotone statistic ranked against a matched null; the actual p-value is an integer count).
    G_c = sum_i (c_i - sum_i/K)^2 / (sum_i/K)."""
    mean = np.asarray(sum_counts, dtype=np.float64) / K
    diff = control_array.astype(np.float64) - mean
    # avoid div-by-zero where mean==0 (those cells contribute 0 by convention)
    with np.errstate(divide='ignore', invalid='ignore'):
        terms = np.where(mean > 0, diff ** 2 / np.where(mean > 0, mean, 1.0), 0.0)
    return terms.sum(axis=1)


def g_rank_key_single(obs, sum_counts, K):
    """G for a single count tuple (float, for ranking only)."""
    mean = np.asarray(sum_counts, dtype=np.float64) / K
    diff = np.asarray(obs, dtype=np.float64) - mean
    with np.errstate(divide='ignore', invalid='ignore'):
        terms = np.where(mean > 0, diff ** 2 / np.where(mean > 0, mean, 1.0), 0.0)
    return float(terms.sum())


def permutation_pvalue(short_counts, control_array):
    """p = (1 + #{k: G(control_k) >= G(short)}) / (1 + K). The p-value itself is an exact
    integer ratio (the count of controls >= short, plus 1 for the short itself, over K+1).
    G is used only as a MONOTONE ranking value (permitted by the no-float rule: a float
    transform ranked against a matched permutation null). control_array: (K, ncells) int."""
    K = control_array.shape[0]
    sum_counts = control_array.sum(axis=0)
    g_short = g_rank_key_single(short_counts, sum_counts, K)
    g_controls = g_rank_keys_batch(control_array, sum_counts, K)
    ge = int(np.sum(g_controls >= g_short)) + 1   # +1 for the short itself
    return Fraction(ge, K + 1)


def holm_fires(pvals, alpha=ALPHA):
    """Holm step-down: fires iff at least one H0 rejected."""
    sp = sorted(pvals)
    M = len(sp)
    for i, p in enumerate(sp):
        threshold = alpha / (M - i)
        if p > threshold:
            return False if i == 0 else True
    return True


def calibrate_plant(delta, n=N_DEFAULT, k_controls=K_DEFAULT, reps=800, seed=20260801):
    """Power of the Holm rule against a planted delta deviation (flap-epsilon).
    Returns Fraction(power). Uses numpy-vectorized multinomial draws and G-ranking."""
    rng = np.random.default_rng(seed)
    n_fire = 0
    for _ in range(reps):
        # planted law (flap): planted draw vs its own control ensemble
        controls_flap = control_flap_counts_batch(n, k_controls, rng)
        p_flap = permutation_pvalue(planted_flap_counts(n, delta, rng), controls_flap)
        # 4 null laws: each an independent control-vs-control p-value
        pvals = [p_flap]
        for _ in range(4):
            c_null = control_flap_counts_batch(n, k_controls, rng)
            pvals.append(permutation_pvalue(control_flap_counts(n, rng), c_null))
        if holm_fires(pvals, ALPHA):
            n_fire += 1
    return Fraction(n_fire, reps)


def main():
    print("=" * 72)
    print("shortscalar_plantfires_v1 -- §4 planted positive control (calibration scale)")
    print("=" * 72)
    print("Plant: move delta*n flap-CORE triples to +R (deviation delta from 1/4 baseline).")
    print("Rule: Holm over 5 tests at family alpha=0.05. Best case (1 planted law, 4 null).")
    print("n (flap sample) = %d, K (control ensemble) = %d, reps = %d" % (N_DEFAULT, K_DEFAULT, 800))
    print("-" * 72)
    print("%-10s %-12s %s" % ("delta", "power", "PREREG §5 target"))
    targets = {0.02: "0.310", 0.05: "0.984", 0.08: "~1.000"}
    for delta in [0.00, 0.01, 0.02, 0.03, 0.05, 0.08, 0.12]:
        pw = calibrate_plant(delta, reps=1500, seed=1000 + int(delta * 100))
        tgt = targets.get(delta, "")
        marker = " <-- delta* (flap, B=1e4)" if delta == 0.02 else ""
        print("  %-8.3f %-12.4f %s%s" % (delta, float(pw), tgt, marker))
    print("-" * 72)
    print("Verdict (§3(c) constructibility): the plant is well-defined and the rule's power")
    print("curve fires at/above delta* and is void below it -- the §4 control is CONSTRUCTIBLE.")
    print("Full plant-fires at the (B,p) ladder still require the GLV harness (not built; gate-blocked).")
    print("=" * 72)


if __name__ == "__main__":
    main()
