"""
lrc_owner_set_harness_v2.py

Corrected dynamic ownership-set harness for Lemma BR (Boundary Run Bound).

KEY CORRECTION over v1:
  safe(e,b) = { a ∈ Z_n : runner e covers a at fiber b }
  A_b = ∩_{e ∈ E_non} safe(e,b)  — residues safe for ALL non-divisor runners
  Good fiber: A_b ≠ ∅  (at least one simultaneous witness exists)
  Bad  fiber: A_b = ∅   (no simultaneous witness)

Definitions:
  start_run = initial consecutive BAD fibers from b_lo
  end_run   = final  consecutive BAD fibers up to  b_hi
  B_safe    = |{b ∈ B_div : A_b ≠ ∅}| = good fiber count
  budget    = (|C| − (n−1)) / 2

Lemma BR:  start_run ≤ budget
Equivalence: B_safe = |C| − 2·start_run ≥ n−1   (when bad fibers = initial + final run only)

Guardrail examples:
  G1: n=6, E_non={1,2,3,5},       L=30    → singly-covered start
  G2: n=6, E_non={3,5,7,15,17},   L=3570  → full double-coverage, start_run=357 expected
"""

from math import gcd
from itertools import combinations


# ---------------------------------------------------------------------------
# Core: safe set of residues for runner e at fiber b
# ---------------------------------------------------------------------------

def safe_set(e, b, L, n):
    """
    Return set of residues a ∈ Z_n that are safe for runner e at fiber b.

    k = aL + b is safe for runner e iff:
        L ≤ (e * k) mod (nL) ≤ (n-1) * L

    This means runner e is NOT in the dangerous zone (close to 0) at time k/N.
    """
    N = n * L
    result = set()
    for a in range(n):
        x = (e * (a * L + b)) % N
        if L <= x <= (n - 1) * L:
            result.add(a)
    return frozenset(result)


# ---------------------------------------------------------------------------
# A_b = intersection of safe sets over all E_non runners
# ---------------------------------------------------------------------------

def A_b(e_non, b, L, n):
    """
    A_b = ∩_{e ∈ E_non} safe(e, b)

    The set of residues simultaneously safe for all non-divisor runners at fiber b.
    |A_b| > 0 ↔ fiber b is GOOD (contributes to B_safe / x_0).
    |A_b| = 0 ↔ fiber b is BAD.
    """
    if not e_non:
        return frozenset(range(n))
    result = safe_set(e_non[0], b, L, n)
    for e in e_non[1:]:
        result = result & safe_set(e, b, L, n)
    return result


# ---------------------------------------------------------------------------
# B_div fibers
# ---------------------------------------------------------------------------

def compute_b_div(n, L):
    """
    B_div for single divisor runner e=n: fibers b with L ≤ n*b ≤ (n-1)*L.
    (n*(aL+b) mod nL = n*b for all a, so this is a-independent.)
    """
    return [b for b in range(L) if L <= n * b <= (n - 1) * L]


# ---------------------------------------------------------------------------
# Main analysis
# ---------------------------------------------------------------------------

def analyze(n, E_non, L, label="", verbose=True):
    """Full Lemma BR analysis for one tuple."""
    e_non = sorted(E_non)
    b_div = compute_b_div(n, L)
    if not b_div:
        if verbose:
            print(f"  {label}: B_div is empty, skip.")
        return None

    b_lo = b_div[0]
    b_hi = b_div[-1]
    C_size = len(b_div)
    budget = (C_size - (n - 1)) / 2

    if verbose:
        print(f"\n{'='*64}")
        print(f"  {label or 'Config'}: n={n}, E_non={e_non}, L={L}")
        print(f"  b_div: [{b_lo}, {b_hi}], |C|={C_size}")
        print(f"  Budget (|C|-(n-1))/2 = ({C_size}-{n-1})/2 = {budget:.3f}")

    # Compute good/bad classification for every fiber
    good = []
    bad_set_fibers = []
    witnesses = {}  # b -> A_b (only for good fibers)
    for b in b_div:
        ab = A_b(e_non, b, L, n)
        if ab:
            good.append(b)
            witnesses[b] = ab
        else:
            bad_set_fibers.append(b)

    B_safe = len(good)

    # start_run = initial consecutive bad fibers from b_lo
    start_run = 0
    for b in b_div:
        if b in bad_set_fibers or not (b in witnesses):
            start_run += 1
        else:
            break
    # Actually need to check b_div in order
    start_run = 0
    for b in b_div:
        ab = A_b(e_non, b, L, n)
        if not ab:
            start_run += 1
        else:
            break

    # end_run = final consecutive bad fibers up to b_hi
    end_run = 0
    for b in reversed(b_div):
        ab = A_b(e_non, b, L, n)
        if not ab:
            end_run += 1
        else:
            break

    # First good fiber (= b_break in the plan)
    b_break = None
    for b in b_div:
        ab = A_b(e_non, b, L, n)
        if ab:
            b_break = b
            break

    br_ok = start_run <= budget

    if verbose:
        print(f"  B_safe    = {B_safe} (good fibers)")
        print(f"  C_bad     = {C_size - B_safe} (bad fibers)")
        print(f"  start_run = {start_run} (initial BAD run from b_lo)")
        print(f"  end_run   = {end_run}   (final BAD run to b_hi)")
        print(f"  b_break   = {b_break}   (first GOOD fiber)")
        print(f"  symmetric = {'YES' if start_run == end_run else 'NO (check palindrome!)'}")
        print(f"  Lemma BR: start_run={start_run} ≤ budget={budget:.3f}? {'✓ OK' if br_ok else '✗ FAIL'}")
        print(f"  B_safe={B_safe} ≥ n-1={n-1}? {'✓ OK' if B_safe >= n-1 else '✗ FAIL'}")

        # Show coverage details at b_lo
        print(f"\n  Coverage at b_lo={b_lo}:")
        total_cov = 0
        for e in e_non:
            ss = safe_set(e, b_lo, L, n)
            print(f"    e={e}: safe_set = {sorted(ss)}  (|safe|={len(ss)})")
            total_cov += len(ss)
        print(f"  A_b_lo = {sorted(A_b(e_non, b_lo, L, n))}  (witnesses at b_lo, should be ∅)")
        print(f"  Sum coverage = {total_cov}  (overcovering={total_cov > n})")

        # Show first good fiber
        if b_break is not None:
            ab_break = A_b(e_non, b_break, L, n)
            print(f"\n  First GOOD fiber: b={b_break}, A_b={sorted(ab_break)}")

            # Dynamic critical residue analysis
            # Find b_crit = first fiber where some residue drops to single-owner
            # "owner" = set of runners e for which r ∈ safe_set(e, b) ∩ A_b_complement
            # Actually b_crit in the "replacement-impossibility" sense:
            # b_crit = first b ≥ b_lo where ∃r, |{e: r ∈ safe_set(e,b)}| = 1
            b_crit = None
            for b in b_div[:start_run + 5]:  # Check around the transition
                for r in range(n):
                    owners = [e for e in e_non if r in safe_set(e, b, L, n)]
                    if len(owners) == 1:
                        b_crit = b
                        break
                if b_crit is not None:
                    break
            print(f"  b_crit (first single-owner residue, if any) = {b_crit}")

    # Replacement-impossibility check at b_break
    if verbose and b_break is not None:
        print(f"\n  Replacement-impossibility check at b_break-1={b_break-1 if b_break>b_lo else 'N/A'}:")
        if b_break > b_lo and b_break - 1 in [x for x in b_div]:
            b_prev = b_break - 1
            ab_prev = A_b(e_non, b_prev, L, n)
            ab_at = A_b(e_non, b_break, L, n)
            print(f"    A_{{b_break-1}} = {sorted(ab_prev)} (bad)")
            print(f"    A_{{b_break}}   = {sorted(ab_at)} (good, witnesses={sorted(ab_at)})")
            for r in sorted(ab_at):
                # Which runner(s) just "completed" coverage of r?
                owners_now = [e for e in e_non if r in safe_set(e, b_break, L, n)]
                owners_prev = [e for e in e_non if r in safe_set(e, b_prev, L, n)]
                newly_arrived = [e for e in owners_now if e not in owners_prev]
                print(f"    r={r}: owners at b_break={sorted(owners_now)}, "
                      f"owners at b_break-1={sorted(owners_prev)}, "
                      f"newly arrived={newly_arrived}")

    return {
        'n': n,
        'E_non': tuple(e_non),
        'L': L,
        'C_size': C_size,
        'b_lo': b_lo,
        'b_hi': b_hi,
        'B_safe': B_safe,
        'C_bad': C_size - B_safe,
        'start_run': start_run,
        'end_run': end_run,
        'b_break': b_break,
        'budget': budget,
        'br_ok': br_ok,
        'palindrome': (start_run == end_run),
    }


# ---------------------------------------------------------------------------
# Sweep
# ---------------------------------------------------------------------------

def lcm(a, b):
    return a * b // gcd(a, b)


def lcm_list(lst):
    r = 1
    for x in lst:
        r = lcm(r, x)
    return r


def sweep(n_range=range(3, 8), max_e_factor=3, max_L_mult=None, max_per_n=2000):
    """Sweep all n in n_range, verify Lemma BR, palindrome symmetry."""
    total = 0
    fails_br = []
    fails_palindrome = []
    fails_bsafe = []

    for n in n_range:
        max_e = max_e_factor * n
        target_size = n - 2  # |E_non| for single E_div={n}
        speeds = [e for e in range(1, max_e + 1) if e != n]
        count = 0

        for combo in combinations(speeds, target_size):
            if count >= max_per_n:
                break
            e_all = list(combo) + [n]
            g = e_all[0]
            for x in e_all[1:]:
                g = gcd(g, x)
            if g != 1:
                continue
            L = lcm_list(e_all)
            if max_L_mult and L > max_L_mult * n:
                continue

            r = analyze(n, list(combo), L, verbose=False)
            if r is None:
                continue
            total += 1
            count += 1

            if not r['br_ok']:
                fails_br.append(r)
            if not r['palindrome']:
                fails_palindrome.append(r)
            if r['B_safe'] < n - 1:
                fails_bsafe.append(r)

    print(f"\nSweep complete: {total} tuples")
    print(f"  Lemma BR violations (start_run > budget):    {len(fails_br)}")
    print(f"  Palindrome violations (start_run ≠ end_run): {len(fails_palindrome)}")
    print(f"  B_safe < n-1 violations:                     {len(fails_bsafe)}")

    if fails_br:
        print("\nLemma BR FAILURES:")
        for r in fails_br[:5]:
            print(f"  n={r['n']}, E_non={r['E_non']}, L={r['L']}: "
                  f"start_run={r['start_run']}, budget={r['budget']:.2f}, B_safe={r['B_safe']}")
    if fails_palindrome:
        print("\nPalindrome FAILURES:")
        for r in fails_palindrome[:5]:
            print(f"  n={r['n']}, E_non={r['E_non']}, L={r['L']}: "
                  f"start_run={r['start_run']}, end_run={r['end_run']}")
    if fails_bsafe:
        print("\nB_safe < n-1 FAILURES:")
        for r in fails_bsafe[:5]:
            print(f"  n={r['n']}, E_non={r['E_non']}, L={r['L']}: "
                  f"B_safe={r['B_safe']}, n-1={r['n']-1}")

    return fails_br, fails_palindrome, fails_bsafe


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == '__main__':
    print("=" * 64)
    print("LRC Owner-Set Harness v2 — Corrected Lemma BR Analysis")
    print("=" * 64)

    # Guardrail G1: small example
    analyze(n=6, E_non=[1, 2, 3, 5], L=30, label="G1 (singly-covered start)")

    # Guardrail G2: large start_run expected ~357
    analyze(n=6, E_non=[3, 5, 7, 15, 17], L=3570, label="G2 (double-coverage, large start_run)")

    # Additional examples
    analyze(n=5, E_non=[1, 2, 3], L=30, label="n=5 basic")
    analyze(n=7, E_non=[1, 2, 3, 5, 6], L=210, label="n=7 basic")

    print("\n" + "=" * 64)
    print("Sweep n=3..6 (E_div={n}, speeds up to 3n)")
    print("=" * 64)
    fails_br, fails_pal, fails_bs = sweep(n_range=range(3, 7), max_e_factor=3, max_per_n=1000)
    if not fails_br and not fails_pal and not fails_bs:
        print("\nAll tuples satisfy Lemma BR, palindrome symmetry, and B_safe ≥ n-1. ✓")
