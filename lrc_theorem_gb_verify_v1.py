"""
lrc_theorem_gb_verify_v1.py
============================
Numerical verification of Theorem GB (Generalised Bounded-Ratio Witness).

THEOREM GB: For k runners with speeds 0 < e_1 < ... < e_k and e_k/e_1 <= k,
the time t* = k / ((k+1) * e_k) satisfies ||e_i * t*|| >= 1/(k+1) for all i.

This script verifies the theorem for:
  1. AP configurations at the boundary ratio (e_k / e_1 = k exactly)
  2. AP configurations with ratio < k
  3. Random configurations with ratio < k
  4. Near-boundary cases (ratio = k - epsilon)
  5. Non-AP (clumped) configurations with ratio < k

Uses exact Fraction arithmetic for boundary cases; float for random sweeps.
"""

import csv
import random
from fractions import Fraction


# ---------------------------------------------------------------------------
# Core check
# ---------------------------------------------------------------------------

def lrc_norm(x):
    """||x|| = distance from nearest integer = min(frac(x), 1 - frac(x))."""
    if isinstance(x, Fraction):
        frac = x - int(x)
        if frac < 0:
            frac += 1
        return min(frac, 1 - frac)
    else:
        frac = x % 1.0
        return min(frac, 1.0 - frac)


def check_theorem_gb_exact(speeds_frac, k):
    """
    Verify Theorem GB with exact arithmetic (Fraction).
    speeds_frac: list of k Fraction objects [e_1, ..., e_k], sorted ascending.
    Returns: (witness, all_lonely, min_norm, threshold)
    """
    e1 = speeds_frac[0]
    ek = speeds_frac[-1]
    threshold = Fraction(1, k + 1)

    # Condition: ratio e_k / e_1 <= k
    ratio = ek / e1
    if ratio > k:
        return None, False, None, threshold  # precondition violated

    t_star = Fraction(k, k + 1) / ek

    norms = []
    for e in speeds_frac:
        pos = e * t_star
        n = lrc_norm(pos)
        norms.append(n)

    min_norm = min(norms)
    all_lonely = min_norm >= threshold
    return t_star, all_lonely, min_norm, threshold


def check_theorem_gb_float(speeds_float, k):
    """
    Verify Theorem GB with float arithmetic.
    Returns: (t_star, all_lonely, min_norm, threshold)
    """
    e1 = speeds_float[0]
    ek = speeds_float[-1]
    threshold = 1.0 / (k + 1)

    ratio = ek / e1
    if ratio > k + 1e-12:
        return None, False, None, threshold

    t_star = k / ((k + 1) * ek)

    norms = [lrc_norm(e * t_star) for e in speeds_float]
    min_norm = min(norms)
    all_lonely = min_norm >= threshold - 1e-12
    return t_star, all_lonely, min_norm, threshold


# ---------------------------------------------------------------------------
# Test case generators
# ---------------------------------------------------------------------------

def ap_at_ratio(k, ratio=None):
    """AP with k runners: speeds 1, 1+d, 1+2d, ... where ratio = k * d + 1."""
    if ratio is None:
        ratio = k  # boundary
    d = Fraction(ratio - 1, k - 1) if k > 1 else Fraction(0)
    return [Fraction(1) + i * d for i in range(k)]


def random_speeds_below_ratio(k, max_ratio=None, seed=None):
    """k random speeds in (1, max_ratio], sorted, ratio <= max_ratio."""
    if max_ratio is None:
        max_ratio = k
    rng = random.Random(seed)
    ek = max_ratio  # fix fastest runner at max
    speeds = sorted([1.0] + [1.0 + rng.random() * (ek - 1.0) for _ in range(k - 2)] + [ek])
    return speeds


def clumped_speeds(k):
    """k runners clumped: e_1 = 1, then k-2 runners near 1.5, then e_k = k/2."""
    cluster = [Fraction(3, 2) + Fraction(i, 100) for i in range(k - 2)]
    speeds = [Fraction(1)] + cluster + [Fraction(k, 2)]
    return sorted(speeds)


# ---------------------------------------------------------------------------
# Main verification
# ---------------------------------------------------------------------------

def run_verification():
    results = []
    all_passed = True

    print("=" * 72)
    print("THEOREM GB VERIFICATION")
    print("t* = k / ((k+1) * e_k)  is a lonely witness when e_k/e_1 <= k")
    print("=" * 72)

    # ------------------------------------------------------------------
    # 1. Exact checks: AP at boundary ratio (e_k / e_1 = k exactly)
    # ------------------------------------------------------------------
    print("\n--- 1. AP at boundary ratio (e_k/e_1 = k, exact arithmetic) ---")
    for k in range(2, 12):
        speeds = ap_at_ratio(k, ratio=k)
        ratio = speeds[-1] / speeds[0]
        t_star, ok, min_norm, threshold = check_theorem_gb_exact(speeds, k)
        status = "PASS" if ok else "FAIL"
        if not ok:
            all_passed = False
        print(f"  k={k:2d} | ratio={float(ratio):.4f} | t*={float(t_star):.6f} | "
              f"min||e_i t*||={float(min_norm):.6f} | threshold=1/{k+1}={float(threshold):.6f} | {status}")
        results.append({
            "test_type": "ap_boundary", "k": k, "ratio": float(ratio),
            "t_star": float(t_star), "min_norm": float(min_norm),
            "threshold": float(threshold), "pass": ok
        })

    # ------------------------------------------------------------------
    # 2. Exact checks: AP at ratio = k/2 (well below boundary)
    # ------------------------------------------------------------------
    print("\n--- 2. AP at ratio = k/2 (exact arithmetic) ---")
    for k in range(2, 12):
        ratio = Fraction(k, 2)
        speeds = ap_at_ratio(k, ratio=ratio)
        t_star, ok, min_norm, threshold = check_theorem_gb_exact(speeds, k)
        status = "PASS" if ok else "FAIL"
        if not ok:
            all_passed = False
        print(f"  k={k:2d} | ratio={float(ratio):.4f} | t*={float(t_star):.6f} | "
              f"min||e_i t*||={float(min_norm):.6f} | threshold={float(threshold):.6f} | {status}")
        results.append({
            "test_type": "ap_half_ratio", "k": k, "ratio": float(ratio),
            "t_star": float(t_star), "min_norm": float(min_norm),
            "threshold": float(threshold), "pass": ok
        })

    # ------------------------------------------------------------------
    # 3. Exact checks: clumped configurations
    # ------------------------------------------------------------------
    print("\n--- 3. Clumped configurations (exact arithmetic) ---")
    for k in range(3, 10):
        speeds = clumped_speeds(k)
        ratio = speeds[-1] / speeds[0]
        t_star, ok, min_norm, threshold = check_theorem_gb_exact(speeds, k)
        if t_star is None:
            print(f"  k={k:2d} | ratio={float(ratio):.4f} | PRECONDITION VIOLATED (ratio > k)")
            continue
        status = "PASS" if ok else "FAIL"
        if not ok:
            all_passed = False
        print(f"  k={k:2d} | ratio={float(ratio):.4f} | t*={float(t_star):.6f} | "
              f"min||e_i t*||={float(min_norm):.6f} | threshold={float(threshold):.6f} | {status}")
        results.append({
            "test_type": "clumped", "k": k, "ratio": float(ratio),
            "t_star": float(t_star), "min_norm": float(min_norm),
            "threshold": float(threshold), "pass": ok
        })

    # ------------------------------------------------------------------
    # 4. Float sweep: random configurations, k=2..10, 100 trials each
    # ------------------------------------------------------------------
    print("\n--- 4. Random configurations (float, 100 trials per k) ---")
    fail_count = 0
    for k in range(2, 11):
        local_fails = 0
        for seed in range(100):
            speeds = random_speeds_below_ratio(k, max_ratio=k, seed=seed)
            _, ok, min_norm, threshold = check_theorem_gb_float(speeds, k)
            if not ok:
                local_fails += 1
                fail_count += 1
        status = "PASS" if local_fails == 0 else f"FAIL ({local_fails} failures)"
        if local_fails > 0:
            all_passed = False
        print(f"  k={k:2d} | 100 random trials | {status}")

    # ------------------------------------------------------------------
    # 5. Near-boundary: ratio = k - epsilon
    # ------------------------------------------------------------------
    print("\n--- 5. Near-boundary configurations (ratio = k - 1e-6, exact) ---")
    for k in range(2, 10):
        epsilon = Fraction(1, 1_000_000)
        ratio = k - epsilon
        speeds = ap_at_ratio(k, ratio=ratio)
        t_star, ok, min_norm, threshold = check_theorem_gb_exact(speeds, k)
        status = "PASS" if ok else "FAIL"
        if not ok:
            all_passed = False
        margin = min_norm - threshold
        print(f"  k={k:2d} | ratio=k-1e-6 | min_norm - threshold = {float(margin):.2e} | {status}")
        results.append({
            "test_type": "near_boundary", "k": k, "ratio": float(ratio),
            "t_star": float(t_star), "min_norm": float(min_norm),
            "threshold": float(threshold), "pass": ok
        })

    # ------------------------------------------------------------------
    # Summary
    # ------------------------------------------------------------------
    print("\n" + "=" * 72)
    if all_passed:
        print("ALL TESTS PASSED. Theorem GB verified numerically.")
    else:
        print("SOME TESTS FAILED. See above.")
    print("=" * 72)

    # Write CSV
    out_path = "/Users/trentpalelei/Desktop/Math Ex/reports/lrc_theorem_gb_verify_v1_results.csv"
    import os
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=["test_type", "k", "ratio", "t_star", "min_norm", "threshold", "pass"])
        writer.writeheader()
        writer.writerows(results)
    print(f"\nResults written to: {out_path}")

    return all_passed


if __name__ == "__main__":
    run_verification()
