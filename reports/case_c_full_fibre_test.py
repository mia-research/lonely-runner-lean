#!/usr/bin/env python3
"""
Case C full-fibre test: n|q_j for all divisible runners.

The lattice harness only checked b = kL/n (n-1 fibres).
B_div = {L/n, ..., (n-1)L/n} has (n-2)L/n+1 fibres.

For divisible runner speed q_j*n with n|q_j (speed = n^2*m):
  T_div = floor(n^2*m * b / L) at fibre b.
  bad = Z/nZ iff T_div % n == 0 or T_div % n == n-1.
  bad = empty otherwise (TRANSPARENT).

So divisible runner is transparent on (n-2)/n of all fibres.
We need: find a fibre b in B_div where:
  1. All divisible runners are transparent.
  2. Non-divisible runners leave a non-empty miss set.
"""

from math import gcd, lcm
from functools import reduce

def lcm_list(lst):
    return reduce(lcm, lst)

def bad_set_residues(rho, T, n):
    g = gcd(rho, n)
    if g == n:
        Tmod = T % n
        return set(range(n)) if (Tmod == 0 or Tmod == n-1) else set()
    elif g == 1:
        inv = pow(rho, -1, n)
        return {(-T * inv) % n, (-(T+1) * inv) % n}
    else:
        if T % g == 0 or (T+1) % g == 0:
            step = n // g
            return set(range(0, n, step))
        return set()

def full_fibre_search(n, d1, d2, div_qs, verbose=True):
    """
    Search ALL integer fibres b in [L/n, (n-1)L/n] for a safe one.
    Returns (found, first_safe_b, L, stats).
    """
    # Build speed sets
    retained_rho = [r for r in range(1, n) if r not in (d1, d2)]
    # Actual speeds: non-divisible are their residue (q=0), divisible are q_j*n
    # For the fibre analysis with actual speeds:
    # Non-divisible runner with residue rho (q_e=0): actual speed = rho
    # Divisible runner q_j: actual speed = q_j * n
    
    # L = lcm of all speeds
    all_speeds = retained_rho + [q * n for q in div_qs]
    L = lcm_list(all_speeds)
    
    # B_div range
    b_lo = L // n
    b_hi = (n-1) * L // n
    b_range = b_hi - b_lo + 1
    
    if verbose:
        print(f"n={n}, d=({d1},{d2}), div_qs={div_qs}")
        print(f"L={L}, B_div=[{b_lo},{b_hi}], |B_div|={b_range}")
        print(f"Lattice fibres (kL/n): {[k*L//n for k in range(1,n)]}")
    
    safe_count = 0
    first_safe = None
    lattice_set = set(k * L // n for k in range(1, n))
    non_lattice_safe = 0
    
    # Only scan if feasible
    if b_range > 2_000_000:
        print(f"  B_div too large ({b_range}), sampling...")
        # Sample: check every (b_range // 100000) fibres
        step = max(1, b_range // 100000)
        scan_range = range(b_lo, b_hi+1, step)
    else:
        scan_range = range(b_lo, b_hi+1)
    
    for b in scan_range:
        # Compute coverage
        coverage = set()
        div_ok = True
        
        # Non-divisible runners
        for rho in retained_rho:
            T = (rho * b) // L
            bs = bad_set_residues(rho, T, n)
            coverage |= bs
        
        # Divisible runners
        for q_j in div_qs:
            # Actual speed = q_j * n
            T = (q_j * n * b) // L
            bs = bad_set_residues(q_j * n, T, n)
            if len(bs) == n:
                div_ok = False
                break
            coverage |= bs
        
        if div_ok and len(coverage) < n:
            safe_count += 1
            if first_safe is None:
                first_safe = b
                if verbose:
                    miss = set(range(n)) - coverage
                    is_lattice = b in lattice_set
                    print(f"  First safe fibre: b={b} ({'LATTICE' if is_lattice else 'non-lattice'})")
                    print(f"  Miss set: {sorted(miss)}")
                    # Show div runner floor states
                    for q_j in div_qs:
                        T = (q_j * n * b) // L
                        print(f"    div q={q_j}, speed={q_j*n}, T={T}, T%n={T%n}")
            if b not in lattice_set:
                non_lattice_safe += 1
    
    if verbose:
        print(f"  Total safe fibres found: {safe_count}, non-lattice safe: {non_lattice_safe}")
    
    return first_safe is not None, first_safe, L, safe_count

# ─── Test cases ──────────────────────────────────────────────────────────────

print("=" * 70)
print("CASE C: n|q_j for divisible runners (lattice fibres all killed)")
print("=" * 70)

# n=15, both q_j divisible by n=15
print("\n─── n=15, div=[15,30] (both q≡0 mod 15) ───")
full_fibre_search(15, 3, 6, [15, 30])

print("\n─── n=15, div=[15,15*2] = [15,30], drop (5,10) ───")
full_fibre_search(15, 5, 10, [15, 30])

print("\n─── n=15, div=[15,16] (one q=n, one q=n+1) ───")
full_fibre_search(15, 3, 6, [15, 16])

print("\n─── n=15, div=[225,240] = [15^2, 15*16] ───")
full_fibre_search(15, 3, 6, [225, 240])

print("\n─── n=21, div=[21,42] ───")
full_fibre_search(21, 3, 6, [21, 42])

print("\n─── n=21, div=[21,22] ───")
full_fibre_search(21, 3, 6, [21, 22])

print("\n─── n=35, div=[35,70] ───")
full_fibre_search(35, 5, 10, [35, 70], verbose=True)

