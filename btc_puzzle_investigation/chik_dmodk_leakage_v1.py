#!/usr/bin/env python3
"""
chik_dmodk_leakage_v1.py — the frozen run for PREREG_chik_dmodk_leakage_v3.md.

CONFIRMATORY (user-authorised 2026-07-27): the χ_k(x([d]G)) vs (d mod k) channel is
already adjudicated null in the record (leak_test_exact.py target `d%3`;
key_cubic_char_v2.py cubic/sextic lean ~p=0.10 = intrinsic short-interval character
sum, not creator signal). This run is an end-to-end demonstration of the kfold_gate
out-of-sample workflow on that settled-null channel, on UNSEEN data — NOT a novel test.

Frozen spec SHA-256 (PREREG_chik_dmodk_leakage_v3.md):
    feda18a2cd9fbc1c6200c6302465011d4aec1178df04f9e3acf18501a32c7220

Signal path is exact int: feature χ_k(x_d) and target d%k are ints; the ONLY float is
inside mi_bits() (a monotone statistic ranked against a matched permutation null — the
CLAUDE.md carve-out, # noqa: float), the perm-p is an exact integer count, and the gate
verdict is the integer cross-product hits·αden ≤ αnum·trials. check_no_float.py must pass.

DEVIATION (logged): the frozen spec left the D_known "select-bitlen" schedule
underspecified. Pinned here: a single MT19937(S0) stream, bitlen b = 16 + (i mod 145)
∈ [16,160], d = (1<<(b-1)) + rng.randrange(1<<(b-1)) — the canonical draw of
angular_interference_scaling_v1 / evaluate_dsig_residue_claim. Immaterial for a per-point
marginal; disclosed in _DEVIATIONS.
"""
import csv
import os
import random
import numpy as np

from masked_structure_harness_v1 import make_chik, orbit_x, load_82
from angular_interference_scaling_v1 import mi_bits
from ecc_secp256k1 import scalar_mul, N_ORDER, P as SECP_P
from kfold_gate_v1 import KFoldGate, fold_of

HERE = os.path.dirname(os.path.abspath(__file__))

# ---- frozen constants (PREREG v3 §1,§3) ----
S0 = 20260727                 # fold seed + root for all derived seeds; the calendar date
SEED_MT = S0                  # D_known MT19937 stream
SEED_RAND = S0 + 1            # D_rand stream
N_KNOWN = 10000
N_RAND = 10000
N_ORBIT = 40000
B = 4000                      # permutation shuffles
KS = (2, 3, 6)
ALPHA = "0.01"                # gate α, both folds
DATASET_ID = {"known": 0, "rand": 1, "orbit": 2}

chi = {k: make_chik(SECP_P, k) for k in KS}


def feat_of(xs, k):
    return np.array([chi[k](x) if chi[k](x) is not None else 0 for x in xs], dtype=np.int64)


# ================================================================= datasets
def build_known():
    """Single MT19937(S0) stream, select-bitlen -> curve. Returns list of (x_d, d)."""
    rng = random.Random(SEED_MT)
    out = []
    i = 0
    while len(out) < N_KNOWN:
        b = 16 + (i % 145)                      # bitlengths 16..160
        d = (1 << (b - 1)) + rng.randrange(1 << (b - 1))
        i += 1
        xy = scalar_mul(d)
        if xy:
            out.append((xy[0], d))
    return out


def build_rand():
    rng = random.Random(SEED_RAND)
    out = []
    while len(out) < N_RAND:
        d = rng.randrange(1, N_ORDER)           # full range [1,n)
        xy = scalar_mul(d)
        if xy:
            out.append((xy[0], d))
    return out


def build_orbit():
    xs = orbit_x(N_ORBIT)                        # x([i]G), i=1..N_ORBIT
    return [(x, i + 1) for i, x in enumerate(xs)]


# ================================================================= statistic
def perm_hits(feat, targ, k, fold, dataset_id):
    """Exact integer permutation count: #shuffles with MI >= observed (ties -> hit)."""
    raw = mi_bits(feat, targ)
    rng = np.random.default_rng(S0 + 7919 * k + 31 * fold + dataset_id)
    hits = 0
    for _ in range(B):
        if mi_bits(feat, targ[rng.permutation(len(targ))]) >= raw:
            hits += 1
    return hits, raw


def gate_dataset(name, data, k, feature_override=None):
    """Run the both-folds gate for one (dataset,k). feature_override(xs,ds)->feat lets
    the controls inject a planted/graded feature; default = χ_k(x_d)."""
    did = DATASET_ID[name]
    xs_all = [x for x, _ in data]
    d_by_x = {x: d for x, d in data}

    def per_fold(fold, sub_xs):
        ds = [d_by_x[x] for x in sub_xs]
        feat = feature_override(sub_xs, ds) if feature_override else feat_of(sub_xs, k)
        targ = np.array([d % k for d in ds], dtype=np.int64)
        hits, _ = perm_hits(feat, targ, k, fold, did)
        return hits, B

    res = KFoldGate(ALPHA, 2, S0).run(xs_all, per_fold)
    # pooled (context only, not the verdict)
    feat = feature_override(xs_all, [d_by_x[x] for x in xs_all]) if feature_override else feat_of(xs_all, k)
    targ = np.array([d_by_x[x] % k for x in xs_all], dtype=np.int64)
    p_hits, raw = perm_hits(feat, targ, k, 9, did)
    return res, raw, p_hits


def line(name, k, res, raw, p_hits):
    tag = "EMIT" if res.emit else "suppress"
    folds = " ".join(f"f{fo.fold}:{fo.hits}/{fo.trials}{'✓' if fo.passed else '✗'}" for fo in res.folds)
    print(f"    {name:6} chi_{k} vs d%{k}: MI={raw:.4f}b pooled {p_hits}/{B}  "  # noqa: float
          f"[{folds}] => {tag}")
    return res.emit


# ================================================================= controls
def control_C1(known):
    """Positive control: feature = the residue itself. Gate MUST emit (power exists)."""
    print("\n  [C1] positive control — planted leak f_k^+ = d mod k (must EMIT):")
    ok = True
    for k in KS:
        res, raw, ph = gate_dataset("known", known, k,
                                    feature_override=lambda xs, ds, k=k: np.array([d % k for d in ds], dtype=np.int64))
        emit = line("C1", k, res, raw, ph)
        ok = ok and emit
    print(f"    => C1 {'FIRES (instrument has power)' if ok else 'FAILED — abstain per §4c'}")
    return ok


def control_graded(known):
    """Extraction ceiling: overwrite every m-th feature value with the residue.
    Integer fractions only (ε = 1/m). Report smallest ε that EMITs on both folds."""
    print("\n  [graded] extraction ceiling — smallest ε (=1/m) that EMITs (k=3, D_known):")
    for m in (50, 20, 10, 5, 2):                # ε = 2%,5%,10%,20%,50%
        def ov(xs, ds, m=m):
            base = feat_of(xs, 3)
            for j in range(0, len(base), m):
                base[j] = ds[j] % 3
            return base
        res, raw, ph = gate_dataset("known", known, 3, feature_override=ov)
        emit = line(f"eps1/{m}", 3, res, raw, ph)
        if emit:
            print(f"    => extraction ceiling: ε ≈ 1/{m} suffices to EMIT")
            return m
    print("    => no tested ε below 1/2 emits (ceiling above 50% overwrite)")
    return None


# ================================================================= main
def main():
    print("=" * 78)
    print("chik_dmodk_leakage_v1 — frozen run (PREREG v3, SHA feda18a2…)")
    print("CONFIRMATORY on a settled-null channel; UNSEEN data (S0 sets).")
    print("=" * 78)

    print("building datasets (scalar_mul over unseen S0 streams) ...")
    known = build_known()
    rand = build_rand()
    orbit = build_orbit()
    print(f"  D_known N={len(known)}  D_rand N={len(rand)}  D_orbit N={len(orbit)}")

    # controls first
    c1 = control_C1(known)
    control_graded(known)

    # the frozen verdict: gate on the unseen random-style sets
    print("\n  [verdict] χ_k(x_d) vs d mod k, gated (both folds), both random-style sets:")
    emits = {}
    for name, data in (("known", known), ("rand", rand), ("orbit", orbit)):
        emits[name] = {}
        for k in KS:
            res, raw, ph = gate_dataset(name, data, k)
            emits[name][k] = line(name, k, res, raw, ph)

    # §4 determination (pre-committed)
    print("\n" + "=" * 78)
    if not c1:
        print("VERDICT (c) ABSTENTION — C1 did not fire; bank no null. (§4c)")
    else:
        both = [k for k in KS if emits["known"][k] and emits["rand"][k]]
        one = [k for k in KS if emits["known"][k] ^ emits["rand"][k]]
        if both:
            print(f"VERDICT (a) LEAKAGE — gate EMITs on BOTH random sets at k={both}. "
                  f"SURPRISING vs the marginal-null expectation. Freeze witnesses; do NOT "
                  f"narrate as a break; open a replication prereg. (§4a)")
        elif one:
            print(f"VERDICT (b) NULL — non-replicating single-set hit at k={one} "
                  f"(one random set only); NOT scored as leakage. Channel bounded. (§4b)")
        else:
            print("VERDICT (b) NULL — gate SUPPRESSES on both random sets, all k; C1 fired "
                  "so power existed. [EMPIRICAL — SCOPED] no d mod k leakage at N≤1e4, "
                  "k∈{2,3,6}, α=0.01. Bound, not closure. (§4b)")
        print(f"    (D_orbit non-scoring context: emits {[k for k in KS if emits['orbit'][k]]})")
    print("=" * 78)


if __name__ == "__main__":
    main()
