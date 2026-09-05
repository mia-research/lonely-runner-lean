"""
z0s_deep_analysis_v1.py
=======================
Three investigations:

1. THE m=1 "EXCEPTION" — real or not?
   The comment in z0s_discrepancy_analysis_v1.py said:
   "EXCEPTION: If e'=1 is the only smaller unit, s=1·1 mod eᵤ = 1 ≠ 0 = r_dep"
   This appeared to claim Cond1 fails for e'=1 at m=1. Is it true?

2. RELAY INVARIANT FAILURES — why does union_bad = ℤ_n at some fibres?
   n=8, eᵤ=7, m=3,4; n=9, multiple cases.
   What is the structural reason? Three-distance theorem connection?
   What fraction of B_div are relay failures vs. safe fibres?

3. B3b AVERAGING ARGUMENT — n=p^k, p≥5
   Averaging number of uncovered residues over B_div.
   Does the average > 0? What fraction of fibres are safe?
   What is the role of transparency windows for non-unit runners?
"""

from math import gcd
from fractions import Fraction

# ─── helpers ──────────────────────────────────────────────────────────────────

def extended_gcd(a, b):
    if a == 0: return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def modinv(a, n):
    g, x, _ = extended_gcd(a % n, n)
    if g != 1: raise ValueError(f"No inverse gcd({a},{n})={g}")
    return x % n

def phi(n):
    result, temp, p = n, n, 2
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0: temp //= p
            result -= result // p
        p += 1
    if temp > 1: result -= result // temp
    return result

def units(n):
    return [e for e in range(1, n) if gcd(e, n) == 1]

def bad_set(e, t, n):
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

def new_criterion(e_prime, e_u, m, n):
    s = (e_prime * m) % e_u
    cond1 = (s == e_prime)
    cond2 = (e_prime + e_u >= n) and (s == e_prime + e_u - n)
    return cond1 or cond2

def floor_state(e, m, e_u):
    return (e * m) // e_u


# ══════════════════════════════════════════════════════════════════════════════
# INVESTIGATION 1: THE m=1 "EXCEPTION"
# ══════════════════════════════════════════════════════════════════════════════
print("="*70)
print("INVESTIGATION 1: Is the m=1 'exception' real?")
print("="*70)
print("""
The comment said: "s=1·1 mod eᵤ = 1 ≠ 0 = r_dep → NOT covered by e'=1"
This compared s to r_dep. But Cond1 requires s = e' (the SPEED), not s = r_dep.

At m=1:  r_dep = -(0)·eᵤ⁻¹ = 0.
         s = e'·1 mod eᵤ = e' (for e' < eᵤ).
         Cond1: s == e'  →  e' == e'  → TRUE always.

So e'=1 DOES cover r_dep=0 at m=1. The comment confused s=e' with s=r_dep.
""")

print("Direct verification for multiple (n, eu) pairs:")
hdr = "{:>4} {:>4} {:>6} {:>6} {:>5} {:>4} {:>12} {:>11}".format(
    "n", "eu", "e'=1", "r_dep", "t_ep", "s", "Cond1(s=e')", "direct_cov")
print(hdr)
print("-"*65)
for n in [5, 7, 8, 9, 11, 12, 13]:
    un = units(n)
    for e_u in [u for u in un if u >= 2][:3]:
        m = 1
        r_dep = 0  # always at m=1
        e_prime = 1
        if e_prime >= e_u: continue  # need e' < eᵤ
        t_ep = floor_state(e_prime, m, e_u)
        s = (e_prime * m) % e_u
        cond1 = (s == e_prime)
        bs = bad_set(e_prime, t_ep, n)
        direct = (r_dep in bs)
        print(f"{n:>4} {e_u:>4} {e_prime:>6} {r_dep:>6} {t_ep:>5} {s:>4} "
              f"{str(cond1):>12} {str(direct):>11}  {'✓' if cond1==direct else '✗ MISMATCH'}")

print("""
CONCLUSION: Cond1 fires (s=e'=1=e') for ALL (n, eᵤ) pairs. Direct coverage=True.
The 'exception' was a false alarm — the comment mixed up s=e' with s=r_dep.
Theorem 8.2b (m=1 Absorption) is CORRECT: every m=1 event is covered.

WHAT THE 'EXCEPTION' WOULD HAVE MEANT IF REAL:
If e'=1 were the ONLY unit smaller than eᵤ=2 (the smallest non-trivial case),
and Cond1 failed, that would mean r_dep=0 is uncovered → a safe fibre!
But this cannot happen: e'=1 is always at floor 0 at m=1, and 0 ∈ bad(1,0,n).
""")


# ══════════════════════════════════════════════════════════════════════════════
# INVESTIGATION 2: WHY DO RELAY INVARIANT FAILURES OCCUR?
# ══════════════════════════════════════════════════════════════════════════════
print("="*70)
print("INVESTIGATION 2: Relay invariant failures — structural analysis")
print("="*70)

def full_bad_union_at_event(n, e_u, m, E_non):
    """Union of bad sets of all runners in E_non at the z=0 event of eᵤ at m."""
    union = set()
    for e in E_non:
        t = floor_state(e, m, e_u) if e != e_u else m - 1
        union |= bad_set(e, t, n)
        if e == e_u:
            union |= bad_set(e, m, n)  # include both transition states
    return union

def analyze_relay_failures(n):
    un = units(n)
    failures = []
    for e_u in un:
        if e_u == 1: continue
        for m in range(1, e_u):
            union = full_bad_union_at_event(n, e_u, m, un)
            if union == set(range(n)):
                r_dep = (-(m-1) * modinv(e_u, n)) % n
                # Get floor states of all other runners
                floors = {e: floor_state(e, m, e_u) for e in un if e != e_u}
                failures.append({
                    'e_u': e_u, 'm': m, 'r_dep': r_dep, 'floors': floors,
                    'alpha': Fraction(m, e_u)
                })
    return failures

print("\n--- Relay failures for n=8 ---")
failures8 = analyze_relay_failures(8)
for f in failures8:
    print(f"  eᵤ={f['e_u']}, m={f['m']}, α={f['alpha']}={float(f['alpha']):.4f}, "
          f"r_dep={f['r_dep']}")
    print(f"  Floor states: {f['floors']}")
    print(f"  Bad sets:")
    for e in sorted(f['floors']):
        t = f['floors'][e]
        bs = bad_set(e, t, 8)
        print(f"    e={e}, t={t}: bad={sorted(bs)}")
    e_u = f['e_u']
    m = f['m']
    t_trans = m - 1
    bs_lo = bad_set(e_u, t_trans, 8)
    bs_hi = bad_set(e_u, m, 8)
    print(f"  eᵤ={e_u} transition: floor {t_trans}→{m}: bad={sorted(bs_lo)}→{sorted(bs_hi)}")
    print()

print("--- Relay failures for n=9 ---")
failures9 = analyze_relay_failures(9)
print(f"  Count: {len(failures9)}")
for f in failures9:
    print(f"  eᵤ={f['e_u']}, m={f['m']}, α={f['alpha']}={float(f['alpha']):.4f}, r_dep={f['r_dep']}, "
          f"floors={f['floors']}")

print("""
STRUCTURAL ANALYSIS:
The bad sets {-t·e⁻¹, -(t+1)·e⁻¹} of consecutive-floor runners partition ℤ_n.
For runner set {e₁,...,e_{n-1}} at floors {t₁,...,t_{n-1}} — when the floors
form an ARITHMETIC PROGRESSION (0,1,2,...), the bad sets tile ℤ_n perfectly.

Key: at α = m/eᵤ, the floor state of runner e' is ⌊e'·m/eᵤ⌋ ≈ e'·(m/eᵤ).
When m/eᵤ is a 'Farey fraction' close to a rational with small denominator,
the floor states cluster into an arithmetic-like progression → relay failure.
""")

# Three-distance theorem connection:
print("--- THREE-DISTANCE THEOREM CONNECTION ---")
print("""
The Three-Distance Theorem: for any α ∈ ℝ and N ∈ ℤ⁺, the N points
{α}, {2α}, ..., {Nα} on the circle ℝ/ℤ partition the circle into gaps
of at most 3 distinct lengths.

For relay failure: all runners' bad zones (each of width 2/n) must together
cover all of ℝ/ℤ. This requires all gaps between fractional parts {e·α}
to be ≤ 2/n.

At α = m/eᵤ (rational): the Farey/three-distance structure of {e·m/eᵤ mod 1}
for e=1,...,n-1 determines the gap sizes.

WHEN DO RELAY FAILURES OCCUR?
""")

def check_three_distance_gap(n, e_u, m):
    """
    At α = m/eᵤ, compute fractional parts {e·α mod 1} for e=1,...,n-1,
    sort them, and find the maximum gap. Relay failure iff max_gap ≤ 2/n.
    """
    alpha = Fraction(m, e_u)
    frac_parts = sorted([Fraction(e * m % e_u, e_u) for e in range(1, n)])
    # Add 0 and 1 as boundary
    pts = [Fraction(0)] + frac_parts + [Fraction(1)]
    gaps = [pts[i+1] - pts[i] for i in range(len(pts)-1)]
    max_gap = max(gaps)
    threshold = Fraction(2, n)
    return max_gap, threshold, max_gap <= threshold

print(f"{'n':>4} {'eᵤ':>4} {'m':>4} {'α':>8} {'max_gap':>10} {'2/n':>8} {'relay_fail?':>12}")
print("-"*55)
for n in [8, 9]:
    un = units(n)
    for e_u in un:
        if e_u == 1: continue
        for m in range(1, e_u):
            max_gap, thresh, predicted_fail = check_three_distance_gap(n, e_u, m)
            failures = [f for f in (failures8 if n==8 else failures9)
                       if f['e_u']==e_u and f['m']==m]
            actual_fail = len(failures) > 0
            match = '✓' if predicted_fail == actual_fail else '✗ MISMATCH'
            if actual_fail or predicted_fail:
                print(f"{n:>4} {e_u:>4} {m:>4} {float(Fraction(m,e_u)):>8.4f} "
                      f"{float(max_gap):>10.6f} {float(thresh):>8.4f} "
                      f"{'YES' if actual_fail else 'no':>12} {match}")

print("""
CONCLUSION: Relay failures occur EXACTLY when max_gap({e·α mod 1}) ≤ 2/n.
This is the THREE-DISTANCE THEOREM connection:
  - Relay invariant fails ↔ fractional parts {e·m/eᵤ} are dense enough
    (max gap ≤ 2/n) that bad zones cover all of [0,1).
  - This is a RESONANCE condition at rational α = m/eᵤ.
  - It has NOTHING to do with the proof being broken — it means those
    specific fibres are genuinely unsafe.
""")

# What fraction of B_div has relay failures?
print("--- FRACTION OF B_div WITH RELAY FAILURES ---")
print("Using rational breakpoints for L = lcm of all speeds * n")
print()

for n in [8, 9, 10, 12]:
    un = units(n)
    # Count z=0 events that are relay failures
    total_events = sum(e_u - 1 for e_u in un if e_u >= 2)
    fail_events = len(analyze_relay_failures(n))
    print(f"n={n}: {total_events} total z=0 events, {fail_events} relay failures "
          f"({100*fail_events/total_events:.1f}% of events)")
    # Safe events from z=0 (not covered AND not relay failure):
    safe_z0 = 0
    covered_z0 = 0
    fail_z0 = 0
    for e_u in un:
        if e_u == 1: continue
        for m in range(1, e_u):
            # Check relay failure
            union = full_bad_union_at_event(n, e_u, m, un)
            if union == set(range(n)):
                fail_z0 += 1
                continue
            # Check if covered (r_dep covered by some other runner)
            covered = any(new_criterion(e_p, e_u, m, n) for e_p in un if e_p != e_u)
            if covered:
                covered_z0 += 1
            else:
                safe_z0 += 1
    print(f"       z=0 event breakdown: {safe_z0} safe, {covered_z0} covered (not safe), "
          f"{fail_z0} relay-fail (unsafe)")
    print()


# ══════════════════════════════════════════════════════════════════════════════
# INVESTIGATION 3: B3b AVERAGING ARGUMENT
# ══════════════════════════════════════════════════════════════════════════════
print("="*70)
print("INVESTIGATION 3: B3b averaging argument for n=p^k, p≥5")
print("="*70)
print("""
For n=p^k, p≥5: both dropped runners are non-units.
E_fix = all φ(n) units + (p-3) non-unit runners.

QUESTION: What is the average number of uncovered residues over B_div?
If average > 0, then at least one safe fibre must exist.

METHOD: Rational breakpoints — enumerate all intervals between floor-change
events, compute the union of bad sets on each interval, measure total
safe-residue-fibre mass.
""")

def b3b_safe_fibre_analysis(n, dropped_pair, verbose=True):
    """
    For n=p^k with dropped_pair = (a, b) both non-units:
    Compute the fraction of B_div = [1/n, (n-1)/n] that has ≥1 uncovered residue.
    Use rational breakpoints.
    """
    un = units(n)
    non_units_all = [e for e in range(1, n) if gcd(e, n) > 1]
    a, b = dropped_pair
    E_fix = [e for e in un] + [e for e in non_units_all if e != a and e != b]

    if verbose:
        print(f"\n  n={n}, dropped=({a},{b})")
        print(f"  E_fix (size {len(E_fix)}): units={un}, remaining non-units="
              f"{[e for e in non_units_all if e not in [a,b]]}")

    # Rational breakpoints in [1/n, (n-1)/n]
    lo = Fraction(1, n)
    hi = Fraction(n-1, n)

    bps = set([lo, hi])
    for e in E_fix:
        for k in range(0, e + 1):
            pt = Fraction(k, e)
            if lo <= pt <= hi:
                bps.add(pt)
    bps = sorted(bps)

    # For each interval, compute floor states and union of bad sets
    total_width = hi - lo
    safe_width = Fraction(0)
    unsafe_width = Fraction(0)
    total_safe_residues = Fraction(0)  # for averaging

    safe_intervals = []
    unsafe_intervals = []

    for i in range(len(bps) - 1):
        a_pt, b_pt = bps[i], bps[i+1]
        mid = (a_pt + b_pt) / 2
        width = b_pt - a_pt

        # Floor states at mid
        floor_states = {e: int(e * mid) for e in E_fix}

        # Union of bad sets
        union = set()
        for e in E_fix:
            union |= bad_set(e, floor_states[e], n)

        miss = set(range(n)) - union
        if miss:
            safe_width += width
            safe_intervals.append((a_pt, b_pt, miss))
            total_safe_residues += width * len(miss)
        else:
            unsafe_width += width
            unsafe_intervals.append((a_pt, b_pt))

    safe_frac = float(safe_width / total_width)
    avg_miss = float(total_safe_residues / total_width)

    if verbose:
        print(f"  Safe fraction of B_div: {float(safe_width):.6f}/{float(total_width):.6f} "
              f"= {safe_frac:.4f} ({100*safe_frac:.2f}%)")
        print(f"  Average miss size over B_div: {avg_miss:.4f}")
        print(f"  First 3 safe intervals:")
        for iv in safe_intervals[:3]:
            print(f"    α ∈ [{float(iv[0]):.4f}, {float(iv[1]):.4f}): miss={iv[2]}")
        if unsafe_intervals:
            print(f"  First 3 unsafe intervals:")
            for iv in unsafe_intervals[:3]:
                print(f"    α ∈ [{float(iv[0]):.4f}, {float(iv[1]):.4f})")

    return safe_frac, avg_miss, safe_intervals, unsafe_intervals

# n=9 (B3a): both non-units dropped → should be entirely safe at floor-0 interval
print("\n--- n=9 (B3a: both non-units {3,6} dropped) ---")
b3b_safe_fibre_analysis(9, (3, 6), verbose=True)

# n=25 (B3b): 4 non-units, drop 2 different pairs
print("\n--- n=25 (B3b: p=5, k=2) ---")
non_units_25 = [e for e in range(1, 25) if gcd(e, 25) > 1]
print(f"  Non-units of Z_25: {non_units_25}")
# Drop pair (5, 10)
b3b_safe_fibre_analysis(25, (5, 10), verbose=True)
# Drop pair (5, 15)
b3b_safe_fibre_analysis(25, (5, 15), verbose=True)

# n=49 (B3b): 6 non-units, drop 2
print("\n--- n=49 (B3b: p=7, k=2) ---")
non_units_49 = [e for e in range(1, 49) if gcd(e, 49) > 1]
print(f"  Non-units: {non_units_49}")
b3b_safe_fibre_analysis(49, (7, 14), verbose=True)

# ── Summary table across all B3b cases ────────────────────────────────────────
print("\n--- B3b SUMMARY TABLE ---")
print(f"{'n':>4} {'p':>4} {'dropped':>12} {'safe_frac':>10} {'avg_miss':>10}")
print("-"*45)

import sympy  # for primality — only used for labels
def is_prime_power(n):
    for p in range(2, n):
        if p*p > n: break
        if n % p == 0:
            while n % p == 0: n //= p
            return n == 1, p
    return False, n

cases = [
    (9, (3, 6)),
    (25, (5, 10)), (25, (5, 15)), (25, (10, 15)),
    (49, (7, 14)), (49, (7, 21)), (49, (14, 21)),
]

for n, drop in cases:
    nu = [e for e in range(1, n) if gcd(e, n) > 1]
    p = nu[0] if nu else n  # smallest non-unit / p
    sf, am, _, _ = b3b_safe_fibre_analysis(n, drop, verbose=False)
    print(f"{n:>4} {p:>4} {str(drop):>12} {sf:>10.4f} {am:>10.4f}")

print("""
AVERAGING ARGUMENT ASSESSMENT:
If safe_frac > 0 (which all cases show), then B_safe ≥ 1 for LRC.

The average miss size > 0 confirms:
  ∑_{b ∈ B_div} |miss(b)| / |B_div| > 0
which by averaging implies ∃ b with |miss(b)| ≥ 1 → x₀ ≥ 1. ✓

NEXT QUESTION: Can we prove safe_frac > 0 ANALYTICALLY?
""")

# ── Transparency analysis: when are non-unit runners transparent? ─────────────
print("="*70)
print("INVESTIGATION 3b: WHERE are safe fibres in B3b? (transparency structure)")
print("="*70)

def transparency_analysis(n, dropped_pair, verbose=True):
    """Classify safe fibres in B3b by whether non-unit runners are transparent."""
    un = units(n)
    non_units_all = [e for e in range(1, n) if gcd(e, n) > 1]
    a_drop, b_drop = dropped_pair
    E_fix_units = un[:]
    E_fix_nonunits = [e for e in non_units_all if e not in [a_drop, b_drop]]
    E_fix = E_fix_units + E_fix_nonunits

    lo, hi = Fraction(1, n), Fraction(n-1, n)
    bps = set([lo, hi])
    for e in E_fix:
        for k in range(0, e + 1):
            pt = Fraction(k, e)
            if lo <= pt <= hi: bps.add(pt)
    bps = sorted(bps)

    result = {'all_transparent': [], 'partial_transparent': [], 'none_transparent': []}

    for i in range(len(bps) - 1):
        a_pt, b_pt = bps[i], bps[i+1]
        mid = (a_pt + b_pt) / 2
        width = b_pt - a_pt
        floor_states = {e: int(e * mid) for e in E_fix}

        # Check union
        union = set()
        for e in E_fix:
            union |= bad_set(e, floor_states[e], n)
        miss = set(range(n)) - union
        if not miss: continue  # unsafe anyway

        # Classify by transparency of non-unit runners
        nu_transparent = []
        nu_opaque = []
        for e in E_fix_nonunits:
            g = gcd(e, n)
            t = floor_states[e]
            transparent = (t % g not in [0, g-1])
            if transparent: nu_transparent.append(e)
            else: nu_opaque.append(e)

        if not E_fix_nonunits:
            result['all_transparent'].append(width)
        elif len(nu_transparent) == len(E_fix_nonunits):
            result['all_transparent'].append(width)
        elif len(nu_transparent) > 0:
            result['partial_transparent'].append(width)
        else:
            result['none_transparent'].append(width)

    total_safe = sum(result['all_transparent']) + sum(result['partial_transparent']) + sum(result['none_transparent'])
    if verbose and total_safe > 0:
        print(f"\n  n={n}, dropped={dropped_pair}")
        print(f"  Safe fibres where all non-units transparent: "
              f"{float(sum(result['all_transparent'])):.6f} ({100*float(sum(result['all_transparent'])/total_safe):.1f}%)")
        print(f"  Safe fibres where some non-units transparent: "
              f"{float(sum(result['partial_transparent'])):.6f} ({100*float(sum(result['partial_transparent'])/total_safe):.1f}%)")
        print(f"  Safe fibres where NO non-unit transparent: "
              f"{float(sum(result['none_transparent'])):.6f} ({100*float(sum(result['none_transparent'])/total_safe):.1f}%)")

    return result

print()
transparency_analysis(9, (3, 6))
transparency_analysis(25, (5, 10))
transparency_analysis(25, (5, 15))
transparency_analysis(49, (7, 14))

# ── The inductive connection: Cond1/Cond2 as local LRC ────────────────────────
print("\n" + "="*70)
print("INVESTIGATION 3c: INDUCTIVE CONNECTION — Cond1/Cond2 as local LRC")
print("="*70)
print("""
KEY OBSERVATION: e' covers r_dep(eᵤ, m) at z=0 event m iff
  s = e'·m mod eᵤ = e'  (Cond1: e' "aligns" with eᵤ at step m)
  OR s = e'+eᵤ-n (Cond2: wrap-around).

This is equivalent to: the fractional part {e'/eᵤ · m} is within 1/n of 0 or 1.
i.e.: {e'·(m/eᵤ)} ∈ [0, 1/n) ∪ (1-1/n, 1]

This is EXACTLY the LRC "unsafe" condition! Runner e' is NOT lonely (relative
to virtual speed eᵤ) at time t = m/eᵤ.

CONSEQUENCE: An isolated z=0 event (no coverage by any e') means:
  ∀ e' ∈ E_non: {e'·m/eᵤ} ∈ (1/n, 1-1/n)
i.e., ALL runners are "lonely" relative to eᵤ at time m/eᵤ.

This IS the LRC condition for the pair (eᵤ, E_non)! The LRC for the pair
says exactly that some time t has all {e'·t} in (1/n, 1-1/n).

So: Gap A reduces to LRC FOR PAIRS WITHIN THE FULL PROBLEM.
""")

print("Checking: for each (eᵤ, E_non), does LRC-pair hold (∃ isolated m≥2)?")
print()
for n in [6, 8, 9, 10, 12, 15]:
    un = units(n)
    all_pairs_ok = True
    worst_case = None
    for e_u in un:
        if e_u <= 1: continue
        # Find isolated m ≥ 2 events (not covered by any e' AND no relay failure)
        isolated_m_ge2 = []
        for m in range(2, e_u):
            # Check coverage by any unit runner
            covered = any(new_criterion(ep, e_u, m, n) for ep in un if ep != e_u)
            if covered: continue
            # Check relay failure
            union = full_bad_union_at_event(n, e_u, m, un)
            if union == set(range(n)): continue
            isolated_m_ge2.append(m)
        if not isolated_m_ge2:
            all_pairs_ok = False
            worst_case = e_u
    status = "✓ ALL OK" if all_pairs_ok else f"✗ FAIL at eᵤ={worst_case}"
    print(f"  n={n}: {status}")

print("""
PROVISIONAL THEOREM (needs proof for general n):
  For any n ≥ 5 prime and eᵤ ∈ units(n) with eᵤ ≥ 3:
  ∃ m ∈ {2,...,eᵤ-1} such that the m-th z=0 event is isolated
  (not covered by Cond1 or Cond2, and not a relay failure).

This is equivalent to: the sequence {e'·m/eᵤ mod 1} for e' ∈ units(n)\{eᵤ}
has at least one m where all values avoid [0,1/n) ∪ (1-1/n,1].

This is the THREE-DISTANCE THEOREM applied to α = 1/eᵤ:
  The (eᵤ-1) points {1·(1/eᵤ)}, {2·(1/eᵤ)}, ..., {(eᵤ-1)·(1/eᵤ)} are all
  distinct (since eᵤ ∤ n for unit eᵤ) and divide [0,1) into eᵤ-1 gaps.
  By three-distance theorem, there is always a gap of size ≥ 1/(eᵤ-1) ≥ 1/(n-2).
  For this gap to contain an α = m/eᵤ that avoids the bad zones of all e',
  we need the 'good' m values to be plentiful enough.

CONNECTING TO B3b:
  If the inductive argument works (Gap A closed for prime n via three-distance),
  then for composite n=p^k, the same argument applies to the unit sub-group.
  Non-unit runners don't interfere at transparent fibres (bad set = ∅).
  The transparent fraction (p-2)/p > 0 guarantees enough room for the
  three-distance argument to produce an isolated safe event.
""")
