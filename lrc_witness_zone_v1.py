"""
lrc_witness_zone_v1.py
======================
For a given config S of runners (non-11), compute the WITNESS ZONE of each
isolation interval I_k: the subset of I_k where ALL runners in S are isolated.

The witness zone is:  W_k(S) = I_k \\ union_{p in S} B(p)

We compute W_k(S) exactly using interval arithmetic (fractions).
Then find:
1. Which I_k have non-empty witness zones.
2. The minimum witness zone measure across all I_k in {1,...,8}.
3. The adversarial config that minimizes the total witness zone.

Key insight from coverage_table: large runners (p >= 12) intersect ALL I_k,
so the witness zone structure is determined by the specific blocking overlap.
"""

from fractions import Fraction
from itertools import combinations
import random

def isolation_interval(k):
    """I_k = [(11k+1)/121, (11k+10)/121]"""
    return (Fraction(11*k+1, 121), Fraction(11*k+10, 121))

def blocking_intervals_in_Ik(p, k):
    """
    Compute the list of (a, b) sub-intervals of I_k where runner p is BLOCKING.
    B(p) = union_j ((11j-1)/(11p), (11j+1)/(11p))
    """
    lo, hi = isolation_interval(k)
    p_lo = p * lo
    p_hi = p * hi

    # Runner p is blocking at t iff {p*t} in [0,1/11) union (10/11, 1)
    # i.e., there exists integer j s.t. p*t in [11j, 11j+1) or p*t in (11j+10, 11j+11)
    # i.e., t in [j/p, (11j+1)/(11p)) or t in ((11j+10)/(11p), (j+1)/p)

    j_min = int(p_lo)
    j_max = int(p_hi) + 1

    blocking = []
    for j in range(j_min, j_max + 1):
        # Left-blocking: t in [j/p, (11j+1)/(11p))
        lb_lo = Fraction(j, p)
        lb_hi = Fraction(11*j+1, 11*p)
        a = max(lb_lo, lo)
        b = min(lb_hi, hi)
        if b > a:
            blocking.append((a, b))

        # Right-blocking: t in ((11j+10)/(11p), (j+1)/p)
        rb_lo = Fraction(11*j+10, 11*p)
        rb_hi = Fraction(j+1, p)
        a = max(rb_lo, lo)
        b = min(rb_hi, hi)
        if b > a:
            blocking.append((a, b))

    return blocking

def union_intervals(intervals):
    """Merge a list of (a,b) intervals, return sorted merged list."""
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [list(intervals[0])]
    for (a, b) in intervals[1:]:
        if a <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], b)
        else:
            merged.append([a, b])
    return [(a, b) for (a, b) in merged]

def witness_zone(config, k):
    """
    Compute the witness zone of I_k for the given config (list of runner speeds,
    excluding runner 11 which is isolated in all I_k by definition).
    Returns list of (a, b) intervals where ALL runners in config are isolated.
    """
    lo, hi = isolation_interval(k)
    # Start with the full I_k as the witness zone
    witness = [(lo, hi)]

    for p in config:
        if p == 11:
            continue  # runner 11 isolated in I_k by definition
        # Remove blocking intervals from witness zone
        bls = blocking_intervals_in_Ik(p, k)
        # Subtract each blocking interval from witness
        new_witness = []
        for (wlo, whi) in witness:
            remaining = [(wlo, whi)]
            for (blo, bhi) in bls:
                new_remaining = []
                for (a, b) in remaining:
                    if bhi <= a or blo >= b:
                        # No overlap
                        new_remaining.append((a, b))
                    elif blo <= a and bhi >= b:
                        # Fully covered
                        pass
                    elif blo <= a:
                        # Trim left
                        new_remaining.append((bhi, b))
                    elif bhi >= b:
                        # Trim right
                        new_remaining.append((a, blo))
                    else:
                        # Split
                        new_remaining.append((a, blo))
                        new_remaining.append((bhi, b))
                remaining = new_remaining
            new_witness.extend(remaining)
        witness = new_witness

    return witness

def witness_measure(config, k):
    """Total measure of witness zone in I_k."""
    wz = witness_zone(config, k)
    return sum(b - a for (a, b) in wz)

def min_witness_measure(config, k_range=range(1, 9)):
    """Min witness measure over I_k for k in k_range."""
    return min(witness_measure(config, k) for k in k_range)

def all_witness_measures(config, k_range=range(9)):
    """Dict k -> witness_measure(config, k)."""
    return {k: witness_measure(config, k) for k in k_range}

# ================== Analysis ==================

if __name__ == '__main__':
    print("=" * 72)
    print("LRC Witness Zone Analysis v1")
    print("=" * 72)
    print()

    # 1. Single-runner analysis: witness zone of runner 10m in each I_k
    print("[1] Witness zone measure for single mult-10 runner in each I_k")
    print("-" * 72)
    print(f"    {'':>6}  " + "  ".join(f"I_{k}" for k in range(9)))
    for m in range(2, 11):
        p = 10 * m
        measures = [float(witness_measure([p], k)) for k in range(9)]
        row = f"    p={p:>3}:  " + "  ".join(f"{v:.4f}" for v in measures)
        print(row)
    print()

    # 2. Witness zone for key small-runner configs
    print("[2] Witness zone for small runner configs (non-mult-10, non-mult-11)")
    print("-" * 72)
    key_configs = [
        ([6], "runner 6 only"),
        ([7], "runner 7 only"),
        ([8], "runner 8 only"),
        ([9], "runner 9 only"),
        ([6,7,8,9], "runners {6,7,8,9}"),
        ([3,7], "runners {3,7}"),
        ([3,7,20], "runners {3,7,20}"),
        ([2,3,4,5,6,7,8,9], "runners 2..9"),
        ([1,6,7,8,9,16,17,19,46], "extremal config (non-11)"),
    ]
    for config, label in key_configs:
        measures = {k: witness_measure(config, k) for k in range(1, 9)}
        min_m = min(measures.values())
        min_k = min(k for k,v in measures.items() if v == min_m)
        total_pos = sum(1 for v in measures.values() if v > 0)
        print(f"  {label}:")
        print(f"    measures: {[f'I_{k}:{float(v):.4f}' for k,v in measures.items()]}")
        print(f"    min={float(min_m):.6f} at I_{min_k}, positive in {total_pos}/8 intervals")
        print()

    # 3. Does {3,7,20} fully cover I_3?
    print("[3] Detailed witness zone for {3,7,20} in I_3")
    print("-" * 72)
    config = [3, 7, 20]
    k = 3
    wz = witness_zone(config, k)
    lo, hi = isolation_interval(k)
    print(f"  I_3 = [{lo}, {hi}] = [{float(lo):.6f}, {float(hi):.6f}]")
    if wz:
        for (a,b) in wz:
            print(f"  Witness gap: ({a} = {float(a):.6f}, {b} = {float(b):.6f}), width={b-a} = {float(b-a):.6f}")
        print(f"  Total witness measure: {sum(b-a for a,b in wz)} = {float(sum(b-a for a,b in wz)):.6f}")
    else:
        print("  EMPTY witness zone! I_3 fully blocked by {3,7,20}.")
    print()

    # If I_3 is empty, check I_1, I_2, I_4..I_8 for config {1,3,7,11,20}
    print("[4] Full witness zone analysis for config {1,3,7,11,20}")
    print("-" * 72)
    config = [1, 3, 7, 11, 20]
    config_non11 = [p for p in config if p != 11]
    for k in range(1, 9):
        wz = witness_zone(config_non11, k)
        m = sum(b-a for a,b in wz)
        print(f"  I_{k}: witness measure = {m} = {float(m):.6f}  {'WITNESS EXISTS' if m > 0 else 'FULLY BLOCKED'}")
    print()

    # 5. Adversarial search: find configs that minimize min_k witness zone
    print("[5] Adversarial search: minimize min witness zone over I_1..I_8")
    print("-" * 72)

    def adversarial_measure(runner_set):
        """Min witness zone over I_1..I_8 for given non-11 runner set."""
        return min(witness_measure(runner_set, k) for k in range(1, 9))

    # Random adversarial search: 8 non-11, non-p1 runners
    best_min = Fraction(9, 121)  # upper bound (full I_k)
    best_config = None
    n_trials = 5000
    random.seed(42)
    for _ in range(n_trials):
        # Choose 7-9 non-11 non-1 runners from range 2..300
        n = random.randint(6, 9)
        runners = []
        for _ in range(n):
            p = random.randint(2, 300)
            if p not in runners:
                runners.append(p)
        runners = list(set(runners))
        m = adversarial_measure(runners)
        if m < best_min:
            best_min = m
            best_config = runners[:]

    print(f"  Best adversarial config (min witness zone across I_1..I_8):")
    print(f"  Config: {sorted(best_config)}")
    print(f"  Min witness measure: {best_min} = {float(best_min):.8f}")
    print()
    if best_min == 0:
        print("  WARNING: Found config with ZERO witness zone! Contains fully-blocked I_k.")
        # Find which I_k is blocked
        for k in range(1, 9):
            m = witness_measure(best_config, k)
            if m == 0:
                print(f"  I_{k} is fully blocked by {sorted(best_config)}!")
    else:
        print("  All tested configs have positive witness zone in at least one I_k. ✓")
    print()

    # 6. Targeted adversarial: try to cover all of I_1..I_8 with 8 runners
    print("[6] Targeted adversarial: try to simultaneously block ALL of I_1..I_8")
    print("-" * 72)
    print("  Using greedy cover + random restart...")
    best_total_blocked = Fraction(0)
    best_greedy = None
    total_target = sum(Fraction(9, 121) for _ in range(8))  # total width of I_1..I_8

    for trial in range(500):
        # Greedy: add runners one at a time to maximize blocked area
        config = []
        covered_measures = {k: Fraction(0) for k in range(1, 9)}
        random.seed(trial * 7 + 13)

        for step in range(8):
            # Try adding each runner from a candidate list
            candidates = random.sample(range(2, 200), min(50, 198))
            best_gain = Fraction(-1)
            best_p = None
            for p in candidates:
                if p == 11 or p % 11 == 0:
                    continue
                new_measures = {}
                for k in range(1, 9):
                    new_wz = witness_zone(config + [p], k)
                    new_measures[k] = sum(b-a for a,b in new_wz)
                gain = sum(Fraction(9,121) - new_measures[k] for k in range(1,9)) - \
                       sum(Fraction(9,121) - covered_measures[k] for k in range(1,9))
                if gain > best_gain:
                    best_gain = gain
                    best_p = p
            if best_p:
                config.append(best_p)
                for k in range(1, 9):
                    wz = witness_zone(config, k)
                    covered_measures[k] = Fraction(9,121) - sum(b-a for a,b in wz)

        total_blocked = sum(covered_measures.values())
        if total_blocked > best_total_blocked:
            best_total_blocked = total_blocked
            best_greedy = config[:]

    print(f"  Best greedy config: {sorted(best_greedy)}")
    # Compute final witness zones
    for k in range(1, 9):
        wz = witness_zone(best_greedy, k)
        m = sum(b-a for a,b in wz)
        print(f"  I_{k}: witness measure = {float(m):.6f}  {'BLOCKED!' if m == 0 else f'gap={float(m):.6f}'}")
    min_w = min(witness_measure(best_greedy, k) for k in range(1,9))
    print(f"  Min witness measure: {min_w} = {float(min_w):.8f}")
    print()

    # 7. The gap threshold: smallest interval width that runner p could fully block
    print("[7] Gap threshold analysis")
    print("-" * 72)
    print("  Runner p can fully block a contiguous sub-interval of I_k of width >= 2/(11p)")
    print("  I_k width = 9/121 ≈ 0.07438")
    print()
    print("  For runner p to ALONE fully cover I_k:")
    print("  Need gap(p) = 9/(11p) >= 9/121 iff p <= 11.")
    print("  So p <= 10 runners can potentially fully cover a SPECIFIC I_k (if aligned).")
    print("  p >= 12 runners always leave witness gaps within any I_k.")
    print()

    # For each p <= 10, which I_k can p fully cover?
    for p in range(2, 11):
        if p % 10 == 0 or p % 11 == 0:
            continue
        for k in range(1, 9):
            wz = witness_zone([p], k)
            m = sum(b-a for a,b in wz)
            if m == 0:
                print(f"  Runner {p} fully covers I_{k}! (witness zone = 0)")

    # 8. What's the minimum witness zone achievable in a SINGLE I_k?
    print()
    print("[8] Minimum witness zone in I_k: minimum over all 8-runner configs")
    print("-" * 72)
    best_per_k = {}
    for k_target in range(1, 9):
        best_m = Fraction(9, 121)
        best_cfg = None
        # Try combining runners to cover I_k_target
        random.seed(k_target * 17)
        for trial in range(2000):
            n = random.randint(3, 8)
            runners = list(set(random.randint(2, 150) for _ in range(n)))
            runners = [p for p in runners if p % 11 != 0]
            if not runners:
                continue
            m = witness_measure(runners, k_target)
            if m < best_m:
                best_m = m
                best_cfg = runners[:]
        best_per_k[k_target] = (best_m, best_cfg)
        print(f"  I_{k_target}: min witness measure = {float(best_m):.6f}  "
              f"{'(ZERO — fully blocked!)' if best_m == 0 else ''}"
              f"  best config: {sorted(best_cfg) if best_cfg else 'N/A'}")

    print()
    zero_k = [k for k,( m,_) in best_per_k.items() if m == 0]
    if zero_k:
        print(f"  Intervals that CAN be fully blocked: {zero_k}")
        # For each fully-blockable I_k, check if REMAINING I_k have positive witness zones
        for k_target in zero_k:
            _, blocking_cfg = best_per_k[k_target]
            print(f"\n  For config blocking I_{k_target} ({sorted(blocking_cfg)}):")
            for k in range(1, 9):
                if k == k_target:
                    print(f"    I_{k}: BLOCKED (by design)")
                    continue
                m = witness_measure(blocking_cfg, k)
                print(f"    I_{k}: witness measure = {float(m):.6f}")
    else:
        print("  No interval can be fully blocked by any tested runner set. ✓")
    print()

    # 9. Theoretical lower bound on witness zone
    print("[9] Theoretical lower bound on witness zone width")
    print("-" * 72)
    print("  I_k width = 9/121")
    print("  Each runner p covers at most 2/11 fraction of I_k (2 blocking zones of width 2/(11p))")
    print("  With N runners, minimum witness zone width >= (9/121) * (1 - N*2/11) if non-overlapping")
    print()
    for N in range(1, 10):
        lb = Fraction(9, 121) * max(0, 1 - N * Fraction(2, 11))
        ub = Fraction(9, 121)
        print(f"  N={N}: lower bound = {float(lb):.6f} = {lb}")
        if lb <= 0:
            print(f"         (naive bound not useful for N >= 6)")
            break
