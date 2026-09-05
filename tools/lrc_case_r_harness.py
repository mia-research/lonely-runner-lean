"""
lrc_case_r_harness.py
=====================
Investigates Case R> of the Lonely Runner Conjecture for n=11.

For commensurable (integer) speeds p1 < p2 < ... < p10 with p10/p1 > 10,
does there always exist t > 0 with ||p_i * t|| >= 1/11 for all i?

Uses exact rational arithmetic (fractions.Fraction) throughout.
"""

import random
from fractions import Fraction
from math import gcd
from functools import reduce


# ── helpers ──────────────────────────────────────────────────────────────────

def frac_part(x: Fraction) -> Fraction:
    """Fractional part of a Fraction."""
    return x - int(x)


def dist_to_nearest_int(x: Fraction) -> Fraction:
    """||x|| = min({x}, 1 - {x})"""
    f = frac_part(x)
    return min(f, Fraction(1) - f)


def is_isolated(speed: int, t: Fraction, n: int = 11) -> bool:
    """True if ||speed * t|| >= 1/n."""
    return dist_to_nearest_int(Fraction(speed) * t) >= Fraction(1, n)


def all_isolated(speeds, t: Fraction, n: int = 11) -> bool:
    """True if all runners are isolated at time t."""
    threshold = Fraction(1, n)
    for p in speeds:
        if dist_to_nearest_int(Fraction(p) * t) < threshold:
            return False
    return True


def min_isolation(speeds, t: Fraction) -> Fraction:
    """min over i of ||p_i * t||."""
    return min(dist_to_nearest_int(Fraction(p) * t) for p in speeds)


# ── core check function ───────────────────────────────────────────────────────

def check_config(speeds, n: int = 11):
    """
    For a speed vector (integers), run the boundary-set method.

    Returns:
        (witness_t_or_None, min_iso_at_witness_or_best, max_gap_J, W0_interval)

    - witness_t_or_None: first critical time where all runners isolated, or None
    - min_iso_at_witness_or_best: min isolation at witness (or best achieved)
    - max_gap_J: max gap in joint isolation set J within [0, 2/p1]
    - W0_interval: (lo, hi) = (1/(n*p1), 10/(n*p1))
    """
    p1 = speeds[0]
    T_cap = Fraction(2, p1)          # cap at 2 periods of runner 1
    threshold = Fraction(1, n)

    # ── 1. Generate all critical times in (0, T_cap] ──
    critical_times = set()
    for p in speeds:
        # Entry times: t = (n*j + 1) / (n * p),  Exit: (n*j + 10) / (n * p)
        # We need t in (0, T_cap], so j >= 0
        j = 0
        while True:
            t_entry = Fraction(n * j + 1, n * p)
            if t_entry > T_cap:
                break
            critical_times.add(t_entry)
            t_exit = Fraction(n * j + (n - 1), n * p)
            if t_exit <= T_cap:
                critical_times.add(t_exit)
            j += 1

    sorted_times = sorted(critical_times)

    # ── 2. W0 interval ──
    W0_lo = Fraction(1, n * p1)
    W0_hi = Fraction(n - 1, n * p1)
    W0 = (W0_lo, W0_hi)

    # ── 3. Search: check each critical time AND midpoints between consecutive
    #             critical times (where isolation status is constant). ──
    # Build list of candidate times: sorted critical times + midpoints
    candidates = []
    if sorted_times:
        # midpoint before first critical time
        mid0 = sorted_times[0] / 2
        if mid0 > Fraction(0):
            candidates.append(mid0)
        for t in sorted_times:
            candidates.append(t)
        for i in range(len(sorted_times) - 1):
            mid = (sorted_times[i] + sorted_times[i + 1]) / 2
            candidates.append(mid)
        # midpoint after last critical time up to T_cap
        mid_last = (sorted_times[-1] + T_cap) / 2
        if mid_last <= T_cap:
            candidates.append(mid_last)

    # ── 4. Find witness and track joint isolation windows ──
    witness_t = None
    best_min_iso = Fraction(0)
    W0_has_witness = False

    # We'll collect joint isolation windows for max_gap_J
    # A joint isolation interval is an interval [a, b] where all runners
    # are isolated. These are determined by critical times.
    # We scan consecutive segments [sorted_times[i], sorted_times[i+1]].

    joint_windows = []   # list of (start, end) Fraction pairs

    # Check at t=0+ (midpoint from 0 to first critical time)
    all_cands_sorted = sorted(set(candidates))

    for t in all_cands_sorted:
        if t <= Fraction(0) or t > T_cap:
            continue
        m_iso = min_isolation(speeds, t)
        if m_iso >= threshold:
            if witness_t is None:
                witness_t = t
                best_min_iso = m_iso
            elif m_iso > best_min_iso:
                best_min_iso = m_iso  # keep best for display; first witness is still first
            # Check W0
            if W0_lo <= t <= W0_hi:
                W0_has_witness = True
        else:
            if m_iso > best_min_iso and witness_t is None:
                best_min_iso = m_iso

    # ── 5. Compute joint isolation windows for max_gap_J ──
    # Scan through [0, T_cap] broken at critical times
    breakpoints = sorted(set([Fraction(0)] + list(critical_times) + [T_cap]))

    window_start = None
    for i in range(len(breakpoints) - 1):
        a = breakpoints[i]
        b = breakpoints[i + 1]
        mid = (a + b) / 2
        if mid <= Fraction(0) or mid > T_cap:
            continue
        if all_isolated(speeds, mid, n):
            if window_start is None:
                # Check if a itself is also isolated (it might be a boundary)
                # Start window at a (or a small epsilon after)
                window_start = a
        else:
            if window_start is not None:
                joint_windows.append((window_start, a))
                window_start = None
    if window_start is not None:
        joint_windows.append((window_start, T_cap))

    # ── 6. Compute max_gap_J ──
    # Gap between end of one window and start of next; also gap before first
    # and after last within [0, T_cap].
    max_gap_J = Fraction(0)
    if not joint_windows:
        max_gap_J = T_cap   # no joint isolation at all
    else:
        # gap from 0 to first window start
        gap_before = joint_windows[0][0]
        max_gap_J = max(max_gap_J, gap_before)
        # gaps between consecutive windows
        for i in range(len(joint_windows) - 1):
            gap = joint_windows[i + 1][0] - joint_windows[i][1]
            max_gap_J = max(max_gap_J, gap)
        # gap from last window end to T_cap
        gap_after = T_cap - joint_windows[-1][1]
        max_gap_J = max(max_gap_J, gap_after)

    return witness_t, best_min_iso, max_gap_J, W0, W0_has_witness, joint_windows


# ── printing ─────────────────────────────────────────────────────────────────

def print_result(speeds, label=""):
    p1 = speeds[0]
    p10 = speeds[-1]
    ratio = p10 / p1

    witness_t, best_min_iso, max_gap_J, W0, W0_has_witness, joint_windows = check_config(speeds)

    W0_lo, W0_hi = W0
    W0_size = W0_hi - W0_lo

    if label:
        print(f"  [{label}]")
    print(f"  Config: {tuple(speeds)}  ratio={ratio:.4g}")

    if witness_t is not None:
        print(f"  Witness found: t = {witness_t}  (min_isolation = {float(best_min_iso):.6f})")
    else:
        print(f"  NO WITNESS in critical set — min isolation = {float(best_min_iso):.6f}")

    print(f"  W_0 = [{W0_lo}, {W0_hi}],  witness in W_0: {'YES' if W0_has_witness else 'NO'}")
    print(f"  max_gap(J) = {max_gap_J} ({float(max_gap_J):.6f})  vs  |W_0| = {W0_size} ({float(W0_size):.6f})")
    print(f"  Joint isolation windows (first 5): {joint_windows[:5]}")
    print()

    return witness_t is not None, W0_has_witness, best_min_iso


# ── config generation ─────────────────────────────────────────────────────────

def generate_type_a(num=200, seed=42):
    """Type A: random integer speeds with ratio > 10."""
    rng = random.Random(seed)
    configs = []
    while len(configs) < num:
        p1 = rng.randint(1, 5)
        # p10 in (10*p1, 10*p1 + 50]
        p10 = rng.randint(10 * p1 + 1, 10 * p1 + 50)
        if p10 / p1 <= 10:
            continue
        # Pick 8 distinct integers strictly between p1 and p10
        interior = list(range(p1 + 1, p10))
        if len(interior) < 8:
            continue
        middle = sorted(rng.sample(interior, 8))
        speeds = [p1] + middle + [p10]
        if speeds[0] < speeds[-1] and speeds[-1] / speeds[0] > 10:
            configs.append(speeds)
    return configs


def generate_type_b():
    """Type B: adversarial configs."""
    configs = []

    # Paper example
    c1 = [1, 4, 7, 9, 11, 12, 14, 15, 16, 20]
    configs.append((c1, "paper example"))

    c2 = [1, 5, 8, 10, 13, 14, 16, 18, 19, 22]
    configs.append((c2, "adversarial variant"))

    # Resonant configs for k in {2, 3, 5, 7, 11}
    for k in [2, 3, 5, 7, 11]:
        c = [k * i for i in range(1, 10)] + [10 * k + 1]
        configs.append((c, f"resonant k={k}"))

    return configs


def generate_type_c():
    """Type C: near-boundary configs."""
    configs = [
        ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11],  "ratio=11"),
        ([1, 2, 3, 4, 5, 6, 7, 8, 9, 12],  "ratio=12"),
        ([1, 2, 3, 4, 5, 6, 7, 8, 9, 20],  "ratio=20"),
        ([1, 2, 3, 4, 5, 6, 7, 8, 9, 100], "ratio=100"),
        ([1, 3, 5, 7, 9, 11, 13, 15, 17, 19], "odd speeds ratio=19"),
    ]
    return configs


# ── main ──────────────────────────────────────────────────────────────────────

def main():
    total_tested = 0
    witnesses_found = 0
    no_witness_count = 0
    no_W0_witness_count = 0
    all_min_isos = []

    print("=" * 70)
    print("LRC Case R> Harness  |  n=11  |  Boundary-Set Method")
    print("=" * 70)
    print()

    # ── Type B first (small, adversarial) ──
    print("─" * 70)
    print("TYPE B: Adversarial configs")
    print("─" * 70)
    type_b = generate_type_b()
    for speeds, label in type_b:
        p1, p10 = speeds[0], speeds[-1]
        if p10 / p1 <= 10:
            print(f"  SKIP {label}: ratio {p10/p1:.3f} not > 10")
            continue
        found, w0_ok, m_iso = print_result(speeds, label)
        total_tested += 1
        if found:
            witnesses_found += 1
            all_min_isos.append(float(m_iso))
        else:
            no_witness_count += 1
        if not w0_ok:
            no_W0_witness_count += 1

    # ── Type C ──
    print("─" * 70)
    print("TYPE C: Near-boundary configs")
    print("─" * 70)
    type_c = generate_type_c()
    for speeds, label in type_c:
        p1, p10 = speeds[0], speeds[-1]
        if p10 / p1 <= 10:
            print(f"  SKIP {label}: ratio not > 10")
            continue
        found, w0_ok, m_iso = print_result(speeds, label)
        total_tested += 1
        if found:
            witnesses_found += 1
            all_min_isos.append(float(m_iso))
        else:
            no_witness_count += 1
        if not w0_ok:
            no_W0_witness_count += 1

    # ── Type A (200 random) — batch, less verbose ──
    print("─" * 70)
    print("TYPE A: 200 random configs  (seed=42)")
    print("─" * 70)
    type_a = generate_type_a(200)
    a_witnesses = 0
    a_no_witness = 0
    a_no_W0 = 0
    a_min_isos = []
    hard_cases = []   # configs where no W0 witness or unusual

    for speeds in type_a:
        p1, p10 = speeds[0], speeds[-1]
        witness_t, best_min_iso, max_gap_J, W0, W0_has_witness, _ = check_config(speeds)
        total_tested += 1
        if witness_t is not None:
            a_witnesses += 1
            a_min_isos.append(float(best_min_iso))
            all_min_isos.append(float(best_min_iso))
        else:
            a_no_witness += 1
            no_witness_count += 1
            hard_cases.append(speeds)
        if not W0_has_witness:
            a_no_W0 += 1
            no_W0_witness_count += 1

    witnesses_found += a_witnesses
    print(f"  Witnesses found: {a_witnesses}/200")
    print(f"  No witness found: {a_no_witness}/200")
    print(f"  No witness in W_0: {a_no_W0}/200")
    if a_min_isos:
        print(f"  Min isolation (worst witness): {min(a_min_isos):.6f}")
        print(f"  Mean isolation (witnesses): {sum(a_min_isos)/len(a_min_isos):.6f}")
    if hard_cases:
        print(f"\n  Hard cases (no witness found):")
        for sp in hard_cases[:10]:
            print(f"    {tuple(sp)}  ratio={sp[-1]/sp[0]:.3f}")
        if len(hard_cases) > 10:
            print(f"    ... and {len(hard_cases)-10} more")
    print()

    # ── Summary ──
    print("=" * 70)
    print("=== SUMMARY ===")
    print("=" * 70)
    print(f"Configs tested:         {total_tested}")
    pct = 100.0 * witnesses_found / total_tested if total_tested else 0.0
    print(f"Witnesses found:        {witnesses_found} ({pct:.1f}%)")
    print(f"No witness found:       {no_witness_count}")
    if all_min_isos:
        print(f"Min isolation across all witnesses: {min(all_min_isos):.6f}")
    else:
        print("Min isolation across all witnesses: N/A")
    print(f"Configs where no witness in W_0: {no_W0_witness_count}")
    print()


if __name__ == "__main__":
    main()
