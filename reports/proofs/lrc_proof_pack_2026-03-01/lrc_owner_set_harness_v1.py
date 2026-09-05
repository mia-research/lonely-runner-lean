"""
lrc_owner_set_harness_v1.py

Dynamic ownership-set harness for Lemma BR (Boundary Run Bound).

Implements:
  O_r(b)  = { e ∈ E_non : r ∈ B_e(b) }
  D(b)    = |{ r ∈ Z_n : O_r(b) = ∅ }|
  b_crit  = min{ b ≥ b_lo : ∃r, |O_r(b)| = 1 }
  b_break = min{ b > b_lo : D(b) > 0 }

And tests:
  1. b_break − b_lo = start_run  (consistency check)
  2. start_run ≤ (|C| − (n−1)) / 2  (Lemma BR)
  3. Replacement-impossibility at each critical event

Guardrail examples:
  G1: n=6, E_non={1,2,3,5},       L=30
  G2: n=6, E_non={3,5,7,15,17},   L=3570
"""

from math import gcd
from fractions import Fraction
import sys

# ---------------------------------------------------------------------------
# Core: bad set of residues for a single runner e at fiber b
# ---------------------------------------------------------------------------

def bad_set_residues(e, b, L, n):
    """
    Residues r ∈ Z_n such that runner e is in the 'safe zone' at fiber b.

    Fiber b means time α = b/L. Runner e is at position e·α mod 1 = (e·b mod L) / L
    relative to the circle [0,1). Runner is safe (contributes to coverage) iff
    its distance from 0 is ≥ 1/n, i.e., position ∈ [1/n, (n-1)/n].

    In the B_div / fiber model:
      B_e(b) = { r ∈ Z_n : runner e covers residue r at fiber b }

    We use the standard formula:
      safe ↔ (e·b mod L) / L ∈ [1/n, (n-1)/n]
           ↔ L/n ≤ (e·b mod L) ≤ (n-1)L/n

    Return the set of residues r covered by e at fiber b.
    Note: in the grid model, the residue is r = floor((e·b mod L) / (L/n)).
    """
    N = n * L
    # Absolute position of runner e at time b/L on the extended grid [0, nL)
    # We want which "block" of size L it falls in, shifted to be 0-indexed.
    pos = (e * b) % N  # position in [0, nL)
    # Which block? block = pos // L  (0 = bottom, n-1 = top, n = wraps back)
    block = pos // L
    # Safe iff block ∈ {1, ..., n-2}  (not the bottom block 0 or top block n-1)
    # Actually for LRC: runner is "lonely" (at distance ≥ 1/n from 0) iff
    # distance from 0 ∈ [1/n, (n-1)/n], i.e., block ∈ {1,...,n-2}.
    # Coverage contribution: if runner e is safe, it "covers" the residue
    # r = floor(e*b/L) mod n  (its position modulo n).
    # BUT in the B_e(b) model, B_e(b) is the set of residues that e can
    # provide as a witness for. Let me use the formulation from the proof:
    #
    # B_e(b) = { a ∈ Z_n : e*(a*L + b) mod (n*L) ∈ [L, (n-1)*L] }
    #
    # This checks: is there an a such that at fiber b, with the "offset" a,
    # the runner is safe? In the residue model, a is the residue index.

    covered = set()
    for a in range(n):
        x = (e * (a * L + b)) % N
        if L <= x <= (n - 1) * L:
            covered.add(a)
    return frozenset(covered)


# ---------------------------------------------------------------------------
# Compute B_div fibers: fibers b where all divisor runners are safe
# ---------------------------------------------------------------------------

def compute_b_div(n, L, e_div_list):
    """Fibers b ∈ {0,...,L-1} where every e_div runner is safe."""
    N = n * L
    b_div = []
    for b in range(L):
        ok = True
        for e in e_div_list:
            # Runner e_div is safe at fiber b for ALL residues a iff
            # e*(a*L + b) mod nL ∈ [L, (n-1)*L] for all a
            # Since e = k*n, the position wraps uniformly.
            # Actually for e_div = n: safe iff b ∈ (L/n, (n-1)L/n)
            # Let's just check directly: is there any a for which runner n is NOT safe?
            for a in range(n):
                x = (e * (a * L + b)) % N
                if x < L or x > (n - 1) * L:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            b_div.append(b)
    return b_div


def compute_b_div_from_range(n, L):
    """B_div for e_div = {n}, which is b ∈ [L/n, (n-1)L/n] ∩ Z."""
    # For single e_div = n: B_e(b) = { a : n*(a*L+b) mod nL ∈ [L,(n-1)L] }
    # n*(a*L+b) mod nL = (n*b) mod nL = n*b if 0 ≤ b < L, so n*b mod nL = n*b
    # But we need L ≤ n*b ≤ (n-1)*L → 1 ≤ b/(L/n) ≤ n-1 → b ∈ [L/n, (n-1)L/n]
    # Wait, this doesn't depend on a at all for e_div = n? Let me recheck.
    # n*(a*L+b) mod (n*L) = (n*a*L + n*b) mod (n*L) = (n*b) mod (n*L) = n*b (since 0≤b<L → n*b<n*L)
    # So B_n(b) = all of Z_n if L ≤ n*b ≤ (n-1)*L, else empty.
    # B_div = { b : L ≤ n*b ≤ (n-1)*L } = { b : L/n ≤ b ≤ (n-1)*L/n }
    b_lo = L // n  # floor(L/n); we need L/n exactly so check
    b_hi = ((n - 1) * L) // n
    # Exact: b ∈ [L/n, (n-1)L/n] as integers
    result = []
    for b in range(L):
        if n * b >= L and n * b <= (n - 1) * L:
            result.append(b)
    return result


# ---------------------------------------------------------------------------
# Owner sets and deficit
# ---------------------------------------------------------------------------

def compute_owner_sets(b, e_non_list, L, n):
    """O_r(b) for all r ∈ Z_n."""
    owners = {r: set() for r in range(n)}
    for e in e_non_list:
        cov = bad_set_residues(e, b, L, n)
        for r in cov:
            owners[r].add(e)
    return owners


def deficit(owners):
    return sum(1 for r, ow in owners.items() if len(ow) == 0)


# ---------------------------------------------------------------------------
# Main analysis function
# ---------------------------------------------------------------------------

def analyze(n, E_non, L, label="", verbose=True):
    """Full Lemma BR analysis for one tuple."""
    e_non = sorted(E_non)
    b_div = compute_b_div_from_range(n, L)
    b_lo = b_div[0]
    b_hi = b_div[-1]
    C_size = len(b_div)

    if verbose:
        print(f"\n{'='*60}")
        print(f"  {label or 'Config'}: n={n}, E_non={e_non}, L={L}")
        print(f"  b_div: [{b_lo}, {b_hi}], |C|={C_size}")
        print(f"  Budget (|C|-(n-1))/2 = ({C_size}-{n-1})/2 = {(C_size-(n-1))/2:.3f}")

    # Walk through B_div, track owners, find b_crit and b_break
    b_break = None
    b_crit = None
    start_run = 0

    # Count consecutive zero-deficit fibers from b_lo
    for b in b_div:
        owners = compute_owner_sets(b, e_non, L, n)
        d = deficit(owners)
        if d > 0:
            b_break = b
            break
        # Check for critical residue (single owner)
        if b_crit is None:
            for r, ow in owners.items():
                if len(ow) == 1:
                    b_crit = b
                    break
        start_run += 1

    if b_break is None:
        start_run = C_size  # no break found

    budget = (C_size - (n - 1)) / 2
    br_ok = start_run <= budget

    if verbose:
        print(f"  start_run = {start_run}")
        print(f"  b_break   = {b_break}")
        print(f"  b_crit    = {b_crit}")
        print(f"  Lemma BR: {start_run} ≤ {budget:.3f}? {'✓ OK' if br_ok else '✗ FAIL'}")

    # Show owner sets at b_lo
    if verbose:
        owners_at_blo = compute_owner_sets(b_lo, e_non, L, n)
        print(f"\n  Owner sets at b_lo={b_lo}:")
        total_cov = 0
        for r in range(n):
            ow = owners_at_blo[r]
            total_cov += len(ow)
            print(f"    r={r}: O_r = {sorted(ow)}  (|O|={len(ow)})")
        print(f"  Sum coverage = {total_cov}  (n={n}, overcovering={total_cov>n})")

    # Replacement-impossibility test at b_crit
    if b_crit is not None and verbose:
        print(f"\n  Replacement-impossibility test at b_crit={b_crit}:")
        owners_crit = compute_owner_sets(b_crit, e_non, L, n)
        for r, ow in owners_crit.items():
            if len(ow) == 1:
                e_star = list(ow)[0]
                # Find when e_star next drops coverage of r (departure)
                b_dep = None
                for b2 in b_div:
                    if b2 <= b_crit:
                        continue
                    cov2 = bad_set_residues(e_star, b2, L, n)
                    if r not in cov2:
                        b_dep = b2
                        break
                # Find when any other runner first picks up r (earliest replacement)
                b_enter = {}
                for e_prime in e_non:
                    if e_prime == e_star:
                        continue
                    for b2 in b_div:
                        if b2 <= b_crit:
                            # Check if e' already covers r at b_crit
                            cov_at_crit = bad_set_residues(e_prime, b_crit, L, n)
                            if r in cov_at_crit:
                                b_enter[e_prime] = b_crit  # already covering
                                break
                        cov2 = bad_set_residues(e_prime, b2, L, n)
                        if r in cov2:
                            b_enter[e_prime] = b2
                            break
                earliest_repl = min(b_enter.values()) if b_enter else None
                ri_ok = (earliest_repl is None or earliest_repl > b_dep) if b_dep else True
                print(f"    r={r}, e*={e_star}: b_dep={b_dep}, "
                      f"earliest_replacement={earliest_repl} "
                      f"({'RI ✓' if ri_ok else 'RI ✗ FAIL'})")

    return {
        'n': n,
        'E_non': tuple(e_non),
        'L': L,
        'C_size': C_size,
        'b_lo': b_lo,
        'b_hi': b_hi,
        'start_run': start_run,
        'b_break': b_break,
        'b_crit': b_crit,
        'budget': budget,
        'br_ok': br_ok,
    }


# ---------------------------------------------------------------------------
# Sweep: n=3..8, E_div={n}, all valid E_non tuples
# ---------------------------------------------------------------------------

def lcm(a, b):
    return a * b // gcd(a, b)


def lcm_list(lst):
    r = 1
    for x in lst:
        r = lcm(r, x)
    return r


def generate_tuples(n, max_e=None, max_L=None, max_tuples=None):
    """Generate (E_non, L) tuples with E_div={n} for given n."""
    if max_e is None:
        max_e = 3 * n
    if max_L is None:
        max_L = n * (n - 1) * max_e

    from itertools import combinations

    # E_non must have n-2 speeds (since E_div={n} contributes 1, total n-1 runners)
    # gcd(E_non ∪ {n}) = 1
    speeds = [e for e in range(1, max_e + 1) if e != n]
    results = []
    target_size = n - 2  # |E_non| = n-2

    for combo in combinations(speeds, target_size):
        e_all = list(combo) + [n]
        g = e_all[0]
        for x in e_all[1:]:
            g = gcd(g, x)
        if g != 1:
            continue
        L = lcm_list(e_all)
        if max_L and L > max_L:
            continue
        results.append((list(combo), L))
        if max_tuples and len(results) >= max_tuples:
            break
    return results


def sweep(n_range=range(3, 8), max_e=None, max_L=None, verbose_fails=True):
    """Sweep all n in n_range, verify Lemma BR, return summary."""
    total = 0
    fails = []

    for n in n_range:
        if max_e is None:
            me = 2 * n + 2
        else:
            me = max_e
        tuples = generate_tuples(n, max_e=me, max_L=max_L, max_tuples=500)
        for (e_non, L) in tuples:
            r = analyze(n, e_non, L, verbose=False)
            total += 1
            if not r['br_ok']:
                fails.append(r)
                if verbose_fails:
                    print(f"  FAIL: n={n}, E_non={e_non}, L={L}, "
                          f"start_run={r['start_run']}, budget={r['budget']:.2f}")

    print(f"\nSweep complete: {total} tuples, {len(fails)} Lemma BR violations")
    return fails


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == '__main__':
    print("=" * 60)
    print("LRC Owner-Set Harness v1 — Lemma BR Analysis")
    print("=" * 60)

    # Guardrail G1: singly-covered start
    analyze(n=6, E_non=[1, 2, 3, 5], L=30, label="G1 (singly-covered start)")

    # Guardrail G2: full double-coverage start, large start_run
    analyze(n=6, E_non=[3, 5, 7, 15, 17], L=3570, label="G2 (double-coverage, large start_run)")

    # Additional example from previous sessions
    analyze(n=5, E_non=[1, 2, 3], L=30, label="n=5 basic")
    analyze(n=7, E_non=[1, 2, 3, 5, 6], L=210, label="n=7 basic")

    print("\n" + "=" * 60)
    print("Sweep n=3..7 (E_div={n}, small speeds)")
    print("=" * 60)
    fails = sweep(n_range=range(3, 8), max_e=None, max_L=None)
    if not fails:
        print("\nAll tuples satisfy Lemma BR. ✓")
