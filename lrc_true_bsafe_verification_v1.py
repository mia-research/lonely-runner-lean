#!/usr/bin/env python3
"""
lrc_true_bsafe_verification_v1.py
===================================
Computes the TRUE B_safe under the draft's definition:

  B_safe = #{b ∈ B_div : ∃ r ∈ ℤ_n uncovered by all runners in E_non at fibre b}

where B_div = [n, L-n] and "uncovered" means r ∉ bad_set(e, floor(e·b/L), n).

KEY EFFICIENCY: Between consecutive z=0 event positions, ALL floor states are
constant. So B_div is partitioned into O(φ(n)(n-2)/2) intervals within each
of which the bad-set union is constant. This makes the computation O(φ(n)³)
regardless of L — even for L with 15+ digits.

Outputs:
  - True B_safe for each (n, L)
  - Number of safe intervals vs unsafe intervals
  - Comparison with z=0-events-only lower bound
  - Whether true B_safe ≥ φ(n)(n-2)/2 (the theorem claim)
"""

from math import gcd
from fractions import Fraction


# ── arithmetic helpers ──────────────────────────────────────────────────────

def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x


def modinv(a, n):
    g, x, _ = extended_gcd(a % n, n)
    if g != 1:
        raise ValueError(f"No inverse: gcd({a},{n})={g}")
    return x % n


def euler_phi(n):
    result, temp, p = n, n, 2
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            result -= result // p
        p += 1
    if temp > 1:
        result -= result // temp
    return result


def units_mod_n(n):
    return [e for e in range(1, n) if gcd(e, n) == 1]


def bad_set(e, t, n):
    """
    bad(e, t, n) = Sol(e, -t, n) ∪ Sol(e, -(t+1), n)
    Sol(e, j, n) = {r : e·r ≡ j (mod n)}
    """
    g = gcd(e, n)
    result = set()
    for j in [-t, -(t + 1)]:
        j_mod = j % n
        if j_mod % g == 0:
            try:
                r0 = (j_mod // g) * modinv(e // g, n // g) % (n // g)
                for k in range(g):
                    result.add((r0 + k * (n // g)) % n)
            except ValueError:
                pass
    return result


def lcm_int(a, b):
    return a * b // gcd(a, b)


def lcm_list(lst):
    r = 1
    for x in lst:
        r = lcm_int(r, x)
    return r


# ── true B_safe computation via interval partition ─────────────────────────

def compute_true_bsafe(n, L, E_non=None, verbose=False):
    """
    Compute the TRUE B_safe = #{b ∈ [n, L-n] : some residue uncovered}.

    Method: partition [n, L-n] at all z=0 event positions (where any runner's
    floor state changes). Between consecutive transition points, all floor states
    are constant, so the bad-set union is constant. Count interval widths.

    Returns dict with B_safe, safe intervals, safe fibre count breakdown, etc.
    """
    units = units_mod_n(n)
    active_units = [e for e in units if e > 1]
    if E_non is None:
        E_non = units[:]

    b_lo, b_hi = n, L - n
    if b_lo > b_hi:
        return None

    # ── collect all transition points in [b_lo, b_hi] ──
    # Transition of runner e at step m: b = m*L//e (exact integer since e | L)
    # At this b, floor(e*b/L) changes from m-1 to m.
    transition_points = set()
    transition_points.add(b_lo)        # interval start
    transition_points.add(b_hi + 1)    # sentinel past end

    for e in E_non:
        if e <= 1:
            continue
        if L % e != 0:
            # Can't have clean z=0 events; use floor transitions directly
            # Transition at b where floor(e*b/L) changes: b = ceil(m*L/e) for m≥1
            # This is b such that e*b >= m*L
            m = (e * b_lo + L - 1) // L  # first floor value at b_lo
            while True:
                b_trans = (m * L + e - 1) // e  # ceil(m*L/e)
                if b_trans > b_hi:
                    break
                transition_points.add(b_trans)
                m += 1
        else:
            # Clean z=0 events at b = m*L//e for m=1,...,e-1
            for m in range(1, e):
                b_trans = m * L // e
                if b_lo <= b_trans <= b_hi:
                    transition_points.add(b_trans)

    sorted_pts = sorted(transition_points)

    # ── for each interval [b_k, b_{k+1}-1], compute floor states and check safety ──
    B_safe = 0
    safe_intervals = []
    unsafe_intervals = []

    for i in range(len(sorted_pts) - 1):
        b_start = sorted_pts[i]
        b_end = sorted_pts[i + 1] - 1  # inclusive end
        if b_start > b_hi or b_end < b_lo:
            continue
        b_start = max(b_start, b_lo)
        b_end = min(b_end, b_hi)
        if b_start > b_end:
            continue

        width = b_end - b_start + 1

        # Floor states at b_start (constant throughout [b_start, b_end])
        # f_e = floor(e * b_start / L) — exact integer arithmetic
        # = (e * b_start) // L
        union_bad = set()
        for e in E_non:
            f_e = (e * b_start) // L
            union_bad |= bad_set(e, f_e, n)

        miss = set(range(n)) - union_bad
        if miss:
            B_safe += width
            safe_intervals.append((b_start, b_end, width, miss))
        else:
            unsafe_intervals.append((b_start, b_end, width))

    result = {
        'n': n, 'L': L,
        'B_safe': B_safe,
        'bound': sum(e - 1 for e in active_units),
        'n_transition_pts': len(sorted_pts) - 1,  # number of intervals
        'n_safe_intervals': len(safe_intervals),
        'n_unsafe_intervals': len(unsafe_intervals),
        'safe_intervals': safe_intervals,
        'unsafe_intervals': unsafe_intervals,
        'PASS': B_safe >= sum(e - 1 for e in active_units),
    }
    return result


# ── brute-force check for small L (cross-validation) ───────────────────────

def brute_force_bsafe(n, L, E_non=None):
    """
    Brute-force B_safe by checking every b ∈ [n, L-n].
    Only feasible for small L (< ~10000).
    """
    units = units_mod_n(n)
    if E_non is None:
        E_non = units[:]
    active_units = [e for e in units if e > 1]

    b_lo, b_hi = n, L - n
    if b_lo > b_hi:
        return 0

    B_safe = 0
    for b in range(b_lo, b_hi + 1):
        union_bad = set()
        for e in E_non:
            f_e = (e * b) // L
            union_bad |= bad_set(e, f_e, n)
        if set(range(n)) - union_bad:
            B_safe += 1
    return B_safe


# ── main ────────────────────────────────────────────────────────────────────

def main():
    # n values to test — focus on the "failing" ones: n=10,15,42
    test_cases = [
        # (n, k) pairs
        (6,  10),
        (10,  1),
        (10,  5),
        (12,  1),
        (15,  1),
        (30,  1),
        (42,  1),
    ]

    print("=" * 80)
    print("TRUE B_safe VERIFICATION (full B_div scan via interval partition)")
    print("Theorem 8.3 Sub-case (i): B_safe ≥ φ(n)(n-2)/2 ?")
    print("=" * 80)
    print()

    results = []
    for (n, k) in test_cases:
        units = units_mod_n(n)
        active = [e for e in units if e > 1]
        lcm_u = lcm_list(active) if active else 1
        L = k * lcm_u
        bound = sum(e - 1 for e in active)
        phi_n = euler_phi(n)

        print(f"n={n}, k={k}, L={L}, bound={bound}, B_div=[{n},{L-n}]")

        r = compute_true_bsafe(n, L)
        if r is None:
            print("  B_div empty — skip")
            continue

        pass_s = "PASS ✓" if r['PASS'] else "FAIL ✗"
        print(f"  TRUE B_safe = {r['B_safe']} / bound = {r['bound']}  [{pass_s}]")
        print(f"  Intervals: {r['n_transition_pts']} total "
              f"({r['n_safe_intervals']} safe, {r['n_unsafe_intervals']} unsafe)")

        # Cross-validate with brute force for small L
        if L <= 50000:
            bf = brute_force_bsafe(n, L)
            match = "✓" if bf == r['B_safe'] else "MISMATCH!"
            print(f"  Brute-force check: {bf}  [{match}]")

        # Show unsafe intervals if any
        if r['unsafe_intervals']:
            print(f"  Unsafe intervals (bad-set covers all Z_n):")
            for (bs, be, w) in r['unsafe_intervals'][:5]:
                print(f"    [{bs}, {be}], width={w}")
            if len(r['unsafe_intervals']) > 5:
                print(f"    ... ({len(r['unsafe_intervals'])} total)")
        else:
            print(f"  No unsafe intervals — all fibres in safe intervals.")

        results.append(r)
        print()

    # Summary table
    print("=" * 80)
    print("SUMMARY TABLE")
    print("=" * 80)
    print(f"{'n':>4}  {'k':>4}  {'L':>20}  {'bound':>6}  "
          f"{'true_Bsafe':>11}  {'ratio':>7}  {'PASS':>6}")
    print("-" * 80)
    for r in results:
        ratio_s = f"{r['B_safe']/r['bound']:.4f}" if r['bound'] > 0 else "N/A"
        pass_s = "YES" if r['PASS'] else "NO!"
        print(f"{r['n']:>4}  {r['L']:>24}  {r['bound']:>6}  "
              f"{r['B_safe']:>11}  {ratio_s:>7}  {pass_s:>6}")

    print()
    print("INTERPRETATION:")
    print("  If true B_safe ≥ bound for ALL rows → theorem claim is correct,")
    print("  and the z=0-only lower bound (14,41,236) was an undercount, not a counterexample.")
    print("  If true B_safe < bound for some row → theorem needs restatement.")

    # Extra detail: for n=10 k=1, show the full interval breakdown
    print()
    print("=" * 80)
    print("DETAILED INTERVAL BREAKDOWN: n=10, k=1, L=63")
    print("  (All intervals in B_div=[10,53], showing floor states and coverage)")
    print("=" * 80)
    n, L = 10, 63
    units = units_mod_n(n)
    active = [e for e in units if e > 1]
    E_non = units[:]

    r_detail = compute_true_bsafe(n, L, E_non=E_non, verbose=True)

    # Print each interval with floor states
    b_lo, b_hi = n, L - n
    transition_points = set([b_lo, b_hi + 1])
    for e in E_non:
        if e <= 1 or L % e != 0:
            continue
        for m in range(1, e):
            b_trans = m * L // e
            if b_lo <= b_trans <= b_hi:
                transition_points.add(b_trans)

    sorted_pts = sorted(transition_points)
    print(f"Transition points in B_div: {[p for p in sorted_pts if p <= b_hi]}")
    print()
    print(f"{'Interval':>20}  {'width':>5}  "
          + "  ".join(f"f({e})" for e in E_non if e > 1)
          + f"  {'miss':>20}  status")
    print("-" * 90)

    for i in range(len(sorted_pts) - 1):
        b_start = sorted_pts[i]
        b_end = sorted_pts[i + 1] - 1
        if b_start > b_hi or b_end < b_lo:
            continue
        b_start = max(b_start, b_lo)
        b_end = min(b_end, b_hi)
        if b_start > b_end:
            continue

        width = b_end - b_start + 1
        union_bad = set()
        floor_states = {}
        for e in E_non:
            if e > 1:
                f_e = (e * b_start) // L
                floor_states[e] = f_e
                union_bad |= bad_set(e, f_e, n)
        miss = set(range(n)) - union_bad
        status = "SAFE" if miss else "UNSAFE"

        floor_str = "  ".join(f"{floor_states.get(e, 0):5d}" for e in E_non if e > 1)
        interval_str = f"[{b_start},{b_end}]"
        miss_str = str(sorted(miss)) if miss else "∅"
        print(f"{interval_str:>20}  {width:>5}  {floor_str}  {miss_str:>20}  {status}")

    print()
    print(f"TRUE B_safe = {r_detail['B_safe']}  (sum of widths of safe intervals)")
    print(f"Bound = {r_detail['bound']}")
    print(f"PASS = {r_detail['PASS']}")

    # Also show: what the z=0-events-only method would give
    # (count of unique z=0 fibre positions that are safe)
    z0_fibres = set()
    for e_u in active:
        for m in range(1, e_u):
            b = m * L // e_u
            if b_lo <= b <= b_hi:
                z0_fibres.add(b)
    print()
    print(f"z=0 event fibres (unique): {sorted(z0_fibres)}")
    print(f"Count: {len(z0_fibres)}  (this is what the previous script counted as 'B_safe')")
    print()
    print("CONCLUSION: The previous script's 'B_safe' was counting only z=0 event fibres,")
    print("not the full B_div scan. TRUE B_safe includes safe fibres at ALL positions.")


if __name__ == "__main__":
    main()
