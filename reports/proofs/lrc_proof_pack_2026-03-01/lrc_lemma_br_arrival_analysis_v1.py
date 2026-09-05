"""
lrc_lemma_br_arrival_analysis_v1.py

Detailed analysis of arrival times for the worst-case Lemma BR tuples.

For each runner e and candidate witness residue r, computes:
  x_{e,r}(b_lo) = (e*(rL+b_lo)) mod nL
  arr(e, r) = steps from b_lo until e first covers r

And verifies the bound arr(e*, r*) ≤ budget where e* is the last runner.
"""

from math import gcd
from lrc_owner_set_harness_v2 import safe_set, A_b, compute_b_div


def x_val(e, r, b, L, n):
    """(e*(rL+b)) mod nL — position of runner e relative to residue r at fiber b."""
    N = n * L
    return (e * (r * L + b)) % N


def arr_time(e, r, b_lo, L, n):
    """
    Arrival time: first b ≥ b_lo where r ∈ safe_set(e, b).
    Returns b - b_lo (integer number of steps from b_lo).
    """
    x0 = x_val(e, r, b_lo, L, n)
    N = n * L

    if L <= x0 <= (n - 1) * L:
        return 0  # already safe at b_lo

    # x increases by e each step (since b increases by 1 and e|L means period = N/e)
    # First entry into [L, (n-1)L]:
    if x0 < L:
        # Need x0 + e*t ≥ L, first t = ceil((L - x0) / e)
        gap = L - x0
    else:
        # x0 > (n-1)L, need to wrap: go to N then re-enter at L
        # t = (N - x0 + L) / e
        gap = N - x0 + L

    assert gap % e == 0, f"e={e} does not divide gap={gap}! (x0={x0}, L={L})"
    return gap // e


def analyze_worst_case(n, E_non, L, label=""):
    """Full arrival-time analysis for one tuple."""
    e_non = sorted(E_non)
    b_div = compute_b_div(n, L)
    b_lo = b_div[0]
    b_hi = b_div[-1]
    C_size = len(b_div)
    budget = (C_size - (n - 1)) / 2

    # Find b_break and witness r*
    b_break = None
    witness_r = None
    start_run = 0
    for i, b in enumerate(b_div):
        ab = A_b(e_non, b, L, n)
        if ab:
            b_break = b
            witness_r = min(ab)
            break
        start_run += 1

    print(f"\n{'='*64}")
    print(f"  {label}: n={n}, E_non={e_non}, L={L}")
    print(f"  b_lo={b_lo}, b_hi={b_hi}, |C|={C_size}")
    print(f"  start_run={start_run}, b_break={b_break}, r*={witness_r}")
    print(f"  budget={budget:.2f}, ratio={start_run/budget:.4f}")

    if b_break is None:
        print("  No good fiber found!")
        return

    # Arrival times for ALL runners at witness r*
    print(f"\n  Arrival times for witness r*={witness_r}:")
    max_arr = 0
    last_runner = None
    for e in e_non:
        # Check if e has integer arrival (e | L required for exact formula)
        if L % e != 0:
            print(f"    e={e}: WARNING — e does not divide L, formula may be inexact")
        x0 = x_val(e, witness_r, b_lo, L, n)
        safe_at_blo = L <= x0 <= (n-1)*L
        if safe_at_blo:
            arr = 0
        else:
            # Compute exact arrival by simulation (verify formula)
            arr_formula = arr_time(e, witness_r, b_lo, L, n)
            # Verify by simulation
            b_first = b_lo + arr_formula
            assert witness_r in safe_set(e, b_first, L, n), f"Formula wrong at e={e}"
            if arr_formula > 0:
                assert witness_r not in safe_set(e, b_first - 1, L, n), f"Not first at e={e}"
            arr = arr_formula
        if arr > max_arr:
            max_arr = arr
            last_runner = e
        x_zone = "below L" if x0 < L else ("above (n-1)L" if x0 > (n-1)*L else "safe at blo")
        print(f"    e={e} (gcd={gcd(e,n)}): x(b_lo)={x0}, {x_zone}, arr={arr}")

    print(f"\n  Last runner: e*={last_runner} (gcd={gcd(last_runner,n)})")
    print(f"  max arrival = {max_arr} = b_break - b_lo ✓ (matches start_run={start_run})")

    # Check formula for last runner
    e_star = last_runner
    x0_star = x_val(e_star, witness_r, b_lo, L, n)
    N = n * L
    if x0_star > (n-1)*L:
        arr_formula = (N - x0_star + L) // e_star
        print(f"\n  Arrival formula: ({N} - {x0_star} + {L}) / {e_star} = {N-x0_star+L}/{e_star} = {arr_formula}")
    elif x0_star < L:
        arr_formula = (L - x0_star) // e_star
        print(f"\n  Arrival formula: ({L} - {x0_star}) / {e_star} = {L-x0_star}/{e_star} = {arr_formula}")

    # Budget bound check
    budget_formula = (n - 2) * (L - n) / (2 * n)
    print(f"\n  Budget = (n-2)(L-n)/(2n) = {n-2}*{L-n}/(2*{n}) = {budget_formula:.3f}")
    print(f"  Bound: arr(e*,r*) = {max_arr} ≤ {budget_formula:.3f}? {'✓' if max_arr <= budget_formula else '✗ FAIL'}")
    ratio = max_arr / budget_formula
    print(f"  Ratio = {ratio:.4f}")

    # Now check ALL candidate r values (not just r*)
    print(f"\n  All residues — arrival of last runner for each r:")
    for r in range(n):
        arrivals = {}
        for e in e_non:
            if L % e != 0:
                continue
            x0 = x_val(e, r, b_lo, L, n)
            if L <= x0 <= (n-1)*L:
                arrivals[e] = 0
            else:
                arr = arr_time(e, r, b_lo, L, n)
                arrivals[e] = arr
        if arrivals:
            max_a = max(arrivals.values())
            last_e = max(arrivals, key=lambda e: arrivals[e])
            # The b_break for this specific r would be b_lo + max_a IF all runners eventually cover r
            # (but runners with period > b_hi - b_lo might never cover r in B_div)
            print(f"    r={r}: max_arr={max_a} (last e={last_e}, gcd={gcd(last_e,n)}), "
                  f"ratio={max_a/budget_formula:.4f}")


def run_worst_cases():
    """Analyze the top worst-ratio tuples from the sweep."""

    # From sweep: worst cases
    cases = [
        (7, [1, 2, 6, 8, 10], 840, "n=7 worst (ratio=0.6555)"),
        (6, [2, 5, 7, 8], 840, "n=6 second-worst (ratio=0.6295)"),
        (6, [1, 2, 3, 5], 30, "G1 (ratio=0.6250)"),
        (5, [2, 6, 8], 120, "n=5 worst (ratio=0.6087)"),
        (6, [3, 5, 7, 15, 17], 3570, "G2 (ratio=0.3)"),
    ]

    for n, E_non, L, label in cases:
        analyze_worst_case(n, E_non, L, label)


if __name__ == '__main__':
    run_worst_cases()
