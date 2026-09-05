"""
lrc_case_r_diagnostic.py
========================
Phase 1 diagnostic for Case R> of the Lonely Runner Conjecture (n=11).

For each tested configuration, determines which of Cases 0/1/2 applies and
runs the carry-over analysis to verify Conjecture C1:

  For Case 1 (single blocker b at t* = 10/(11*p1)), Conjecture C1 states:
  For all runners i != b:
      (10*p_i mod 11*p1 - p1) / p_i  >=  (10*p_b mod 11*p1) / p_b

  Equivalently, the carry-over condition (*):
      alpha_i - 1/11 >= p_i * epsilon_b
  where alpha_i = {p_i * t*} and epsilon_b = t* - tau_b = N_b/(11*p1*p_b),
  and N_b = R_b = 10*p_b mod (11*p1).

Uses exact rational arithmetic throughout (fractions.Fraction).
"""

import csv
import sys
import random
from fractions import Fraction
from math import gcd

# ── reuse helpers from harness ─────────────────────────────────────────────

def frac_part(x: Fraction) -> Fraction:
    return x - int(x)

def dist_to_nearest_int(x: Fraction) -> Fraction:
    f = frac_part(x)
    return min(f, Fraction(1) - f)

def all_isolated(speeds, t: Fraction, n: int = 11) -> bool:
    threshold = Fraction(1, n)
    for p in speeds:
        if dist_to_nearest_int(Fraction(p) * t) < threshold:
            return False
    return True

def min_isolation(speeds, t: Fraction) -> Fraction:
    return min(dist_to_nearest_int(Fraction(p) * t) for p in speeds)


# ── core diagnostic function ───────────────────────────────────────────────

def diagnose_config(speeds, n: int = 11):
    """
    Diagnose a Case R> configuration.

    Returns a dict with fields:
      case          : 0, 1, or 2
      blockers      : list of speeds that block at t*
      tau_b         : exit-boundary for single blocker (Case 1 only)
      N_b           : gap numerator = R_b = 10*p_b mod (11*p1) (Case 1)
      epsilon_b     : t* - tau_b (Fraction, Case 1)
      carry_over_ok : True if (*) holds for ALL runners i != b (Case 1)
      carry_over_failures : list of (p_i, alpha_i, shift, residual) for failures
      crossing_runners    : list of p_i that have an entry time in (tau_b, t*)
      tau_max             : max exit-boundary over all blockers (Case 2)
      tau_max_is_witness  : True if tau_max is a valid global witness (Case 2)
      witness_in_W0       : True/False (sanity check)
      p1, t_star, W0_lo, W0_hi : key values
    """
    p1 = speeds[0]
    n_val = n
    threshold = Fraction(1, n_val)

    t_star = Fraction(10, n_val * p1)          # right endpoint of W0
    W0_lo  = Fraction(1, n_val * p1)
    W0_hi  = t_star

    result = {
        'speeds'              : tuple(speeds),
        'p1'                  : p1,
        't_star'              : t_star,
        'W0_lo'               : W0_lo,
        'W0_hi'               : W0_hi,
        'case'                : None,
        'blockers'            : [],
        'tau_b'               : None,
        'N_b'                 : None,
        'R_b'                 : None,
        'epsilon_b'           : None,
        'carry_over_ok'       : None,
        'carry_over_failures' : [],
        'crossing_runners'    : [],
        'tau_max'             : None,
        'tau_max_is_witness'  : None,
        'witness_in_W0'       : None,
    }

    # ── 1. Find blockers at t* ──
    blockers = []
    for p in speeds:
        d = dist_to_nearest_int(Fraction(p) * t_star)
        if d < threshold:
            blockers.append(p)

    result['blockers'] = blockers

    # ── 2. Classify ──
    if len(blockers) == 0:
        result['case'] = 0
        result['witness_in_W0'] = True   # t* itself is the witness, in W0
        return result

    elif len(blockers) == 1:
        result['case'] = 1
        p_b = blockers[0]

        # Compute R_b = 10*p_b mod (11*p1)
        R_b = (10 * p_b) % (11 * p1)
        result['R_b'] = R_b

        # N_b = R_b (key identity proved analytically: N_b = 10*p_b - (11*k0-1)*p1 = R_b)
        # Verify: find k0 = ceil such that tau_b in W0
        # tau_b = (11*k0 - 1)/(11*p_b); we want tau_b in W0
        # 1/(11*p1) <= (11*k0-1)/(11*p_b) <= 10/(11*p1)
        # p_b/(11*p1) <= 11*k0-1 <= 10*p_b/p1 - ... solve for k0
        # From t* = 10/(11*p1) and p_b blocks: t* in (tau_b, tau_b + 2/(11*p_b))
        # => tau_b = t* - epsilon_b where 0 < epsilon_b < 2/(11*p_b)
        # Find k0 as the integer such that (11*k0-1)/(11*p_b) < t* <= (11*k0+1)/(11*p_b)

        # p_b * t* = 10*p_b/(11*p1); floor to find which period we're in
        # at time t*, {p_b * t*} = frac_part(10*p_b/(11*p1)) = R_b/(11*p1)
        # This is in [0, 1/11) (since p_b blocks: dist < 1/11 means frac < 1/11 or > 10/11)
        frac_b = frac_part(Fraction(10 * p_b, 11 * p1))
        # blocker means frac_b < 1/11 or frac_b > 10/11
        if frac_b < threshold:
            # {p_b*t*} = frac_b < 1/11: runner b is near an integer from below
            # The gap is around an integer: exit boundary is the most recent
            # (11*j+10)/(11*p_b) before t*, i.e., {p_b*t*} passed 10/11 recently
            # Actually {p_b*t*} = frac_b < 1/11 means p_b*t* = integer + frac_b
            # The exit boundary of runner b's isolation zone that we just passed is at
            # t_exit = (integer - frac_b)/p_b * something...
            # More precisely: p_b*tau_b = floor(p_b*t*) so tau_b = floor(p_b*t*)/p_b is
            # near 0 boundary. The exit time is (11*k+10)/(11*p_b) just before t* in
            # terms of the j counter.
            # The 11-periodized version: p_b*t* = 11*k0/(11) + frac_b for some k0.
            # k0 = round(11*p_b*t* / 11) = round(p_b*t*)
            # tau_b = (11*k0 - 1)/(11*p_b) = k0/p_b - 1/(11*p_b)
            k0 = int(Fraction(p_b) * t_star)   # floor(p_b * t_star)
            # Check: sometimes need k0+1 if we're just past an integer
            tau_b_candidate = Fraction(11 * k0 - 1, 11 * p_b)
            if not (W0_lo <= tau_b_candidate <= W0_hi):
                k0 = k0 + 1
                tau_b_candidate = Fraction(11 * k0 - 1, 11 * p_b)
        else:
            # frac_b > 10/11: runner b near integer from above
            # The exit boundary is (11*k+10)/(11*p_b) just AFTER t* approaching next integer
            # Actually: {p_b*t*} > 10/11 means p_b*t* = integer - (1 - frac_b)
            # The isolation zone ends at (11*k+10)/(11*p_b), and t* is just past it
            # tau_b is the exit time that runner b just passed
            k0_base = int(Fraction(p_b) * t_star) + 1   # ceiling
            tau_b_candidate = Fraction(11 * k0_base - 1, 11 * p_b)
            k0 = k0_base
            # adjust if needed
            if not (W0_lo <= tau_b_candidate <= W0_hi):
                for delta in range(-5, 6):
                    cand = Fraction(11 * (k0_base + delta) - 1, 11 * p_b)
                    if W0_lo <= cand <= W0_hi and not all_isolated(speeds, cand, n):
                        # Check runner b is exactly at boundary
                        if dist_to_nearest_int(Fraction(p_b) * cand) == threshold:
                            tau_b_candidate = cand
                            k0 = k0_base + delta
                            break

        tau_b = tau_b_candidate
        result['tau_b'] = tau_b

        # Compute epsilon_b = t* - tau_b
        epsilon_b = t_star - tau_b
        result['epsilon_b'] = epsilon_b

        # Verify N_b = R_b identity
        N_b = 10 * p_b - (11 * k0 - 1) * p1
        result['N_b'] = N_b
        # Check identity
        if N_b != R_b:
            result['N_b_equals_R_b'] = False
        else:
            result['N_b_equals_R_b'] = True

        # ── Carry-over analysis ──
        carry_over_ok = True
        carry_over_failures = []
        crossing_runners = []

        for p_i in speeds:
            if p_i == p_b:
                continue   # skip the blocker itself
            if p_i == p1 and dist_to_nearest_int(Fraction(p1) * tau_b) >= threshold:
                continue   # runner 1 isolated at tau_b by virtue of tau_b in W0

            alpha_i = frac_part(Fraction(p_i) * t_star)
            shift   = Fraction(p_i) * epsilon_b
            residual = alpha_i - threshold - shift   # should be >= 0

            # Check for crossing: any entry time of runner i in (tau_b, t*)?
            # Entry times: (11*j+1)/(11*p_i). Find j such that tau_b < (11j+1)/(11pi) < t*
            has_crossing = False
            # j range: 11*j+1 in (11*p_i*tau_b, 11*p_i*t_star)
            lo_j = Fraction(11 * p_i) * tau_b - 1
            hi_j = Fraction(11 * p_i) * t_star - 1
            lo_j_int = int(lo_j) + 1 if lo_j > int(lo_j) else int(lo_j)
            hi_j_int = int(hi_j)
            for j in range(max(0, lo_j_int), hi_j_int + 1):
                entry_t = Fraction(11 * j + 1, 11 * p_i)
                if tau_b < entry_t < t_star:
                    has_crossing = True
                    break

            if has_crossing:
                crossing_runners.append(p_i)
                # In the crossing case, runner i is automatically safe (lands near entry boundary)
                # Verify: {p_i * tau_b} should still be in [1/11, 10/11]
                pos_at_tau = frac_part(Fraction(p_i) * tau_b)
                d_at_tau = dist_to_nearest_int(Fraction(p_i) * tau_b)
                if d_at_tau < threshold:
                    carry_over_ok = False
                    carry_over_failures.append({
                        'p_i': p_i, 'alpha_i': float(alpha_i),
                        'shift': float(shift), 'residual': float(residual),
                        'has_crossing': True, 'pos_at_tau': float(pos_at_tau),
                        'isolated_at_tau': False
                    })
            else:
                # No-crossing case: carry-over condition (*) must hold
                if residual < Fraction(0):
                    carry_over_ok = False
                    carry_over_failures.append({
                        'p_i': p_i, 'alpha_i': float(alpha_i),
                        'shift': float(shift), 'residual': float(residual),
                        'has_crossing': False,
                        'pos_at_tau': float(frac_part(Fraction(p_i) * tau_b)),
                        'isolated_at_tau': dist_to_nearest_int(Fraction(p_i) * tau_b) >= threshold
                    })

        result['carry_over_ok'] = carry_over_ok
        result['carry_over_failures'] = carry_over_failures
        result['crossing_runners'] = crossing_runners

        # Verify tau_b is a valid witness
        result['tau_b_is_witness'] = all_isolated(speeds, tau_b, n)
        result['witness_in_W0'] = (W0_lo <= tau_b <= W0_hi)
        return result

    else:
        # Case 2: multiple blockers
        result['case'] = 2

        # Compute exit-boundaries for all blockers, find tau_max
        tau_vals = []
        for p_b in blockers:
            frac_b = frac_part(Fraction(10 * p_b, 11 * p1))
            if frac_b < threshold:
                k0 = int(Fraction(p_b) * t_star)
            else:
                k0 = int(Fraction(p_b) * t_star) + 1
            tau_b_cand = Fraction(11 * k0 - 1, 11 * p_b)
            # Ensure it's in W0
            if not (W0_lo <= tau_b_cand <= W0_hi):
                # Try k0-1 and k0+1
                for delta in [-1, 1, -2, 2]:
                    cand = Fraction(11 * (k0 + delta) - 1, 11 * p_b)
                    if W0_lo <= cand <= W0_hi:
                        tau_b_cand = cand
                        break
            tau_vals.append((tau_b_cand, p_b))

        tau_max = max(tv[0] for tv in tau_vals) if tau_vals else None
        result['tau_max'] = tau_max
        result['all_tau_b'] = tau_vals

        if tau_max is not None:
            result['tau_max_is_witness'] = all_isolated(speeds, tau_max, n)
            result['witness_in_W0'] = (W0_lo <= tau_max <= W0_hi)
        else:
            result['tau_max_is_witness'] = None
            result['witness_in_W0'] = None

        return result


# ── batch runner ──────────────────────────────────────────────────────────

def generate_type_a(num=200, seed=42):
    """Random Case R> configs (same as harness)."""
    rng = random.Random(seed)
    configs = []
    while len(configs) < num:
        p1 = rng.randint(1, 5)
        p10 = rng.randint(10 * p1 + 1, 10 * p1 + 50)
        if p10 / p1 <= 10:
            continue
        interior = list(range(p1 + 1, p10))
        if len(interior) < 8:
            continue
        middle = sorted(rng.sample(interior, 8))
        speeds = [p1] + middle + [p10]
        if speeds[0] < speeds[-1] and speeds[-1] / speeds[0] > 10:
            configs.append(speeds)
    return configs


def generate_type_a_extra(num=1000, seed=99):
    """Extra random configs for Phase 1 (seed=99)."""
    rng = random.Random(seed)
    configs = []
    while len(configs) < num:
        p1 = rng.randint(1, 8)
        p10 = rng.randint(10 * p1 + 1, 10 * p1 + 100)
        if p10 / p1 <= 10:
            continue
        interior = list(range(p1 + 1, p10))
        if len(interior) < 8:
            continue
        middle = sorted(rng.sample(interior, 8))
        speeds = [p1] + middle + [p10]
        if speeds[0] < speeds[-1] and speeds[-1] / speeds[0] > 10:
            configs.append(speeds)
    return configs


def generate_adversarial():
    configs = []
    configs.append(([1, 4, 7, 9, 11, 12, 14, 15, 16, 20], "paper example"))
    configs.append(([1, 5, 8, 10, 13, 14, 16, 18, 19, 22], "adversarial variant"))
    for k in [2, 3, 5, 7, 11]:
        c = [k * i for i in range(1, 10)] + [10 * k + 1]
        configs.append((c, f"resonant k={k}"))
    configs.append(([1, 2, 3, 4, 5, 6, 7, 8, 9, 11], "ratio=11"))
    configs.append(([1, 2, 3, 4, 5, 6, 7, 8, 9, 12], "ratio=12"))
    configs.append(([1, 2, 3, 4, 5, 6, 7, 8, 9, 20], "ratio=20"))
    configs.append(([1, 2, 3, 4, 5, 6, 7, 8, 9, 100], "ratio=100"))
    configs.append(([1, 3, 5, 7, 9, 11, 13, 15, 17, 19], "odd speeds"))
    return configs


def run_batch(configs, verbose=True):
    """Run diagnostics on a list of speed configs."""
    stats = {
        'total': 0,
        'case0': 0, 'case1': 0, 'case2': 0,
        'c1_ok': 0, 'c1_fail': 0,
        'c2_tau_max_ok': 0, 'c2_tau_max_fail': 0,
        'n_b_eq_r_b': 0, 'n_b_neq_r_b': 0,
        'crossings_found': 0,
        'carry_over_failures_detail': [],
        'case2_tau_max_failures': [],
    }

    for speeds in configs:
        p1, p10 = speeds[0], speeds[-1]
        if p10 / p1 <= 10:
            continue

        d = diagnose_config(speeds)
        stats['total'] += 1
        c = d['case']

        if c == 0:
            stats['case0'] += 1

        elif c == 1:
            stats['case1'] += 1
            if d.get('N_b_equals_R_b', True):
                stats['n_b_eq_r_b'] += 1
            else:
                stats['n_b_neq_r_b'] += 1
            if d['crossing_runners']:
                stats['crossings_found'] += 1
            if d['carry_over_ok']:
                stats['c1_ok'] += 1
            else:
                stats['c1_fail'] += 1
                stats['carry_over_failures_detail'].append(d)
                if verbose:
                    print(f"  [CARRY-OVER FAILURE] {tuple(speeds)}")
                    for f in d['carry_over_failures']:
                        print(f"    runner p_i={f['p_i']}: alpha={f['alpha_i']:.6f} "
                              f"shift={f['shift']:.6f} residual={f['residual']:.6f} "
                              f"crossing={f['has_crossing']} isolated_at_tau={f.get('isolated_at_tau','?')}")

        elif c == 2:
            stats['case2'] += 1
            if d['tau_max_is_witness']:
                stats['c2_tau_max_ok'] += 1
            else:
                stats['c2_tau_max_fail'] += 1
                stats['case2_tau_max_failures'].append(d)
                if verbose:
                    print(f"  [CASE2 TAU_MAX FAIL] {tuple(speeds)}")

    return stats


def print_stats(stats, label=""):
    n = stats['total']
    if label:
        print(f"\n{'='*60}")
        print(f"  {label}")
        print(f"{'='*60}")

    print(f"  Total configs:       {n}")
    print(f"  Case 0 (t* valid):   {stats['case0']} ({100*stats['case0']/n:.1f}%)")
    print(f"  Case 1 (1 blocker):  {stats['case1']} ({100*stats['case1']/n:.1f}%)")
    print(f"  Case 2 (2+ blocker): {stats['case2']} ({100*stats['case2']/n:.1f}%)")

    if stats['case1'] > 0:
        print(f"\n  Case 1 — Carry-Over Analysis:")
        print(f"    N_b = R_b identity holds: {stats['n_b_eq_r_b']}/{stats['case1']}")
        print(f"    Configs with crossing runners: {stats['crossings_found']}/{stats['case1']}")
        print(f"    Carry-over (*) satisfied: {stats['c1_ok']}/{stats['case1']}")
        print(f"    Carry-over (*) FAILED:    {stats['c1_fail']}/{stats['case1']}")

    if stats['case2'] > 0:
        print(f"\n  Case 2 — τ_max Analysis:")
        print(f"    τ_max is valid witness: {stats['c2_tau_max_ok']}/{stats['case2']}")
        print(f"    τ_max FAILED:           {stats['c2_tau_max_fail']}/{stats['case2']}")


# ── main ─────────────────────────────────────────────────────────────────

def main():
    print("=" * 60)
    print("LRC Case R> Carry-Over Diagnostic  |  n=11")
    print("=" * 60)

    all_speeds = []

    # Original seed=42 batch
    type_a_orig = generate_type_a(200, seed=42)
    all_speeds.extend(type_a_orig)

    # Extra seed=99 batch
    type_a_extra = generate_type_a_extra(1000, seed=99)
    all_speeds.extend(type_a_extra)

    # Adversarial
    adversarial = generate_adversarial()
    for speeds, label in adversarial:
        if speeds[-1] / speeds[0] > 10:
            all_speeds.append(speeds)

    print(f"\nTotal configs to test: {len(all_speeds)}")
    print()

    # Run with verbose=True so any failures are immediately visible
    stats = run_batch(all_speeds, verbose=True)
    print_stats(stats, "FULL BATCH RESULTS")

    # Summary verdict
    print()
    print("=" * 60)
    print("=== VERDICT ===")
    print("=" * 60)
    c1_total = stats['case1']
    c2_total = stats['case2']

    if stats['c1_fail'] == 0 and c1_total > 0:
        print(f"✓ Conjecture C1 HOLDS for all {c1_total} Case 1 configs tested.")
        print(f"  Carry-over condition (*): (R_i - p1)/p_i >= R_b/p_b — no counterexample found.")
    elif c1_total == 0:
        print("  No Case 1 configs in batch.")
    else:
        print(f"✗ Conjecture C1 FAILS for {stats['c1_fail']}/{c1_total} Case 1 configs.")
        print("  See details above.")

    if stats['c2_tau_max_fail'] == 0 and c2_total > 0:
        print(f"✓ τ_max strategy works for all {c2_total} Case 2 configs tested.")
    elif c2_total == 0:
        print("  No Case 2 configs in batch.")
    else:
        print(f"✗ τ_max strategy FAILS for {stats['c2_tau_max_fail']}/{c2_total} Case 2 configs.")

    if stats['n_b_neq_r_b'] == 0 and c1_total > 0:
        print(f"✓ N_b = R_b identity CONFIRMED for all {stats['n_b_eq_r_b']} Case 1 configs.")
    elif c1_total > 0:
        print(f"✗ N_b != R_b for {stats['n_b_neq_r_b']} configs — identity does NOT hold universally.")

    print()


if __name__ == "__main__":
    main()
