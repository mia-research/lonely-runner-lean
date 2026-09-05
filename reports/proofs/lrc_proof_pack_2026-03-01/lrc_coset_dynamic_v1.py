"""
lrc_coset_dynamic_v1.py
Dynamic Coset Theorem (DCT) verification and obstruction characterisation.

THEOREM DCT (to verify):
  For runner e, fiber b in Bdiv, floor state t_e(b) = floor(e*b/L):
    B_e(b) = Sol(e, -t_e, n) ∪ Sol(e, -(t_e+1), n)
  where Sol(e, k, n) = {a in Z_n : e*a ≡ k (mod n)}, empty iff gcd(e,n) ∤ k.

KEY STRUCTURAL FACTS TO VERIFY:
  D1 (Non-unit sparsity): g_e > 1 → B_e(b) ≤ 1 coset of H_{g_e} or ∅ at each b.
       Specifically: B_e = ∅ unless g_e | t_e or g_e | (t_e+1).
  D2 (Coverage density): active fibers = 2/g_e fraction of Bdiv.
  D4 (Active coset rotation): each coset visited ≈ M*2/(n/g_e) times over period.
  D5 (G4B-NZ0 compatibility): at coset-transition fibers B_e may be ∅ → rescue.

CHECKS:
  1. DCT validation: bad_set(canonical) == Sol(-t) ∪ Sol(-(t+1)) for every (e,b).
  2. Non-unit sparsity (D1): |B_e(b)| ≤ g_e; at most one Sol non-empty for g_e > 1.
  3. Coset rotation (D4): count coset visits per runner across full period.
  4. D=0 obstruction structure: which runners are active? minimum covering set?
  5. Residue coverage frequency: for odd n, which residue is least-often covered?
  6. LBL status: is the first fiber b=0 always safe? First obstruction position.

Scope: n ∈ {6,8,9,10,12,15} with gcd(E_non)=1, n|L, E_div≠∅ for even n.
"""

from math import gcd, lcm
from fractions import Fraction
from itertools import combinations
import functools
import sys


# ---------------------------------------------------------------------------
# Canonical bad_set — exact copy from lrc_g4b_nonunit_z0_certifier_v1.py L33
# ---------------------------------------------------------------------------

def bad_set_canonical(e: int, b: int, L: int, n: int) -> frozenset:
    """B_e(b) — canonical, inverse-free (ground truth)."""
    N = n * L
    bad = set()
    for a in range(n):
        x = (e * (a * L + b)) % N
        if x < L or x > (n - 1) * L:
            bad.add(a)
    return frozenset(bad)


# ---------------------------------------------------------------------------
# DCT-based bad_set computation
# ---------------------------------------------------------------------------

def sol(e: int, k: int, n: int) -> frozenset:
    """Sol(e, k, n) = {a in Z_n : e*a ≡ k (mod n)}, empty if gcd(e,n) ∤ k."""
    g = gcd(e, n)
    k_mod = k % n
    if k_mod % g != 0:
        return frozenset()
    # Reduce: (e/g)*a ≡ (k/g) (mod n/g), unique solution mod n/g → g solutions mod n
    e_red = e // g
    k_red = k_mod // g
    n_red = n // g
    a0 = (k_red * pow(e_red, -1, n_red)) % n_red
    return frozenset(a0 + i * n_red for i in range(g))


def bad_set_dct(e: int, b: int, L: int, n: int) -> frozenset:
    """B_e(b) via DCT-corrected.

    Canonical derivation: let x = (e*(a*L + b)) % (n*L), j = (e*a + t_e) mod n,
    s_e = (e*b) mod L.  Then x = j*L + s_e.
      Lower bad (x < L):   j=0, always → Sol(e, -t_e, n).
      Upper bad (x>(n-1)L): j=n-1 AND s_e>0 → Sol(e,-(t_e+1),n) if s_e>0 else ∅.
    The s_e>0 guard is the z=0 condition: at a z=0 event (s_e=0) the upper zone
    is inactive (x=(n-1)*L is NOT > (n-1)*L).
    """
    t_e = (e * b) // L
    s_e = (e * b) % L          # fractional remainder; 0 at z=0 events
    lower = sol(e, -t_e, n)
    upper = sol(e, -(t_e + 1), n) if s_e > 0 else frozenset()
    return lower | upper


def floor_state(e: int, b: int, L: int) -> int:
    return (e * b) // L


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def lcm_list(lst):
    r = 1
    for x in lst:
        r = lcm(r, x)
    return r


def subgroup(g: int, n: int) -> frozenset:
    """H_g = {0, n/g, 2n/g, ..., (g-1)*n/g} — subgroup of order g."""
    step = n // g
    return frozenset(i * step for i in range(g))


def is_coset_of_H_g(S: frozenset, g: int, n: int) -> bool:
    """Check whether S is a coset of H_g in Z_n (or empty)."""
    if not S:
        return True
    if len(S) != g:
        return False
    H = subgroup(g, n)
    rep = min(S)
    expected = frozenset((rep + h) % n for h in H)
    return expected == S


def bdiv(L: int, n: int):
    """Bdiv = {0, n, 2n, ..., L-n}."""
    M = L // n
    return [j * n for j in range(M)]


# ---------------------------------------------------------------------------
# Core analysis per tuple
# ---------------------------------------------------------------------------

def analyze_tuple(n: int, e_non: tuple) -> dict:
    """Full DCT + coset analysis for one (n, E_non) tuple."""
    L = lcm_list(list(e_non) + [n])
    M = L // n
    Bdiv = bdiv(L, n)

    results = {
        "n": n,
        "e_non": e_non,
        "L": L,
        "M": M,
        # Validation counters
        "dct_match_violations": 0,       # canonical ≠ DCT
        "d1_nonunit_violations": 0,       # g>1 and both Sols non-empty
        "d1_size_violations": 0,          # |B_e| > g_e
        "d1_coset_violations": 0,         # B_e not a coset of H_g
        # Obstruction
        "obstructed_count": 0,
        "safe_count": 0,
        "max_run": 0,
        "first_obst_j": None,            # first j with D(b)=0
        "first_obst_b": None,
        # D=0 analysis
        "dz_runner_profiles": [],         # for each obst fiber: which runners active
        "min_active_for_dz": None,       # min number of runners active at a D=0 fiber
        # Residue coverage frequency
        "residue_cover_count": [0] * n,
        # Coset rotation
        "coset_visits": {},               # {e: {coset_rep: visit_count}}
    }

    for e in e_non:
        results["coset_visits"][e] = {}

    cur_run = 0
    for b in Bdiv:
        U = set()
        active_runners = []

        for e in e_non:
            B_can = bad_set_canonical(e, b, L, n)
            B_dct = bad_set_dct(e, b, L, n)
            g = gcd(e, n)
            t_e = floor_state(e, b, L)

            # --- DCT match check ---
            if B_can != B_dct:
                results["dct_match_violations"] += 1

            # --- D1: non-unit checks ---
            if g > 1:
                lower_sol = sol(e, -t_e, n)
                upper_sol = sol(e, -(t_e + 1), n)
                # Both non-empty simultaneously?
                if lower_sol and upper_sol:
                    results["d1_nonunit_violations"] += 1
                # Size check
                if len(B_can) > g:
                    results["d1_size_violations"] += 1
                # Coset structure check
                if not is_coset_of_H_g(B_can, g, n):
                    results["d1_coset_violations"] += 1

            # --- Coset rotation tracking ---
            if B_can:
                rep = min(B_can)  # coset representative = minimum element
                cv = results["coset_visits"][e]
                cv[rep] = cv.get(rep, 0) + 1

            U |= B_can
            if B_can:
                active_runners.append(e)

        D = n - len(U)

        # Residue coverage
        for r in U:
            results["residue_cover_count"][r] += 1

        if D == 0:
            results["obstructed_count"] += 1
            cur_run += 1
            if results["max_run"] < cur_run:
                results["max_run"] = cur_run
            j = b // n
            if results["first_obst_j"] is None:
                results["first_obst_j"] = j
                results["first_obst_b"] = b
            # Record which runners are active at this D=0 fiber
            results["dz_runner_profiles"].append(tuple(sorted(active_runners)))
        else:
            results["safe_count"] += 1
            cur_run = 0

    # Minimum active runners at any D=0 fiber
    if results["dz_runner_profiles"]:
        results["min_active_for_dz"] = min(len(p) for p in results["dz_runner_profiles"])

    return results


# ---------------------------------------------------------------------------
# Tuple generation
# ---------------------------------------------------------------------------

def gen_tuples(n: int, max_e: int, max_L: int):
    """
    Generate admissible tuples: gcd(E_non)=1, n|L, |E_non|=n-1.
    For even n: require E_div ≠ ∅ (at least one e with n|e).
    For odd n: no restriction beyond gcd=1 and n|L.
    """
    candidates = [e for e in range(1, max_e + 1) if e % n != 0 or (e // n) in range(1, n)]
    # Actually: include e with gcd(e,n) < n (not full-divisors of wrong kind)
    # Simpler: all positive e up to max_e
    candidates = list(range(1, max_e + 1))

    count = 0
    for combo in combinations(candidates, n - 1):
        combo = tuple(sorted(combo))
        if gcd(*combo) != 1:
            continue
        L = lcm_list(list(combo) + [n])
        if L % n != 0:
            continue
        if L > max_L:
            continue
        # Even n: require E_div
        if n % 2 == 0:
            has_ediv = any(e % n == 0 for e in combo)
            if not has_ediv:
                continue
        # Odd n: require n|L (already checked) and allow any gcd=1 tuple
        yield combo
        count += 1
        if count >= 200:
            break


# ---------------------------------------------------------------------------
# Summary output
# ---------------------------------------------------------------------------

def print_summary(all_results: list, n: int):
    dct_total_viol = sum(r["dct_match_violations"] for r in all_results)
    d1_nonunit_viol = sum(r["d1_nonunit_violations"] for r in all_results)
    d1_size_viol = sum(r["d1_size_violations"] for r in all_results)
    d1_coset_viol = sum(r["d1_coset_violations"] for r in all_results)

    total_tuples = len(all_results)
    total_obst = sum(r["obstructed_count"] for r in all_results)
    total_fibers = sum(r["M"] for r in all_results)
    max_run_all = max((r["max_run"] for r in all_results), default=0)
    b_safe_lt_n = sum(1 for r in all_results if r["safe_count"] < n)
    first_j_lt_n = sum(1 for r in all_results
                       if r["first_obst_j"] is not None and r["first_obst_j"] < n)

    print(f"\n{'='*60}")
    print(f"n = {n}  |  Tuples tested: {total_tuples}  |  Total Bdiv-fibers: {total_fibers}")
    print(f"{'='*60}")
    print(f"\n--- DCT Validation ---")
    print(f"  canonical ≠ DCT violations : {dct_total_viol:>6}  (expect 0)")
    print(f"\n--- Fact D1: Non-unit Sparsity ---")
    print(f"  Both Sols non-empty (g>1)  : {d1_nonunit_viol:>6}  (expect 0)")
    print(f"  |B_e(b)| > g_e violations  : {d1_size_viol:>6}  (expect 0)")
    print(f"  B_e not coset of H_g       : {d1_coset_viol:>6}  (expect 0)")
    print(f"\n--- Obstruction Statistics ---")
    print(f"  Total obstructed fibers    : {total_obst:>6}  / {total_fibers}")
    print(f"  Tuples with B_safe < n     : {b_safe_lt_n:>6}  (want 0 for M≥n scope)")
    print(f"  Max consecutive run        : {max_run_all:>6}")
    print(f"  Tuples with first obst j<n : {first_j_lt_n:>6}  (LBL test: 0 = LBL holds)")

    # Min active runners at D=0
    min_acts = [r["min_active_for_dz"] for r in all_results if r["min_active_for_dz"] is not None]
    if min_acts:
        print(f"  Min runners active at D=0  : {min(min_acts):>6}  (how many runners needed)")

    # Residue coverage: which residue is least covered?
    # Aggregate across all tuples/fibers
    total_cov = [0] * n
    for r in all_results:
        for i in range(n):
            total_cov[i] += r["residue_cover_count"][i]
    min_cov_r = min(range(n), key=lambda i: total_cov[i])
    print(f"\n--- Residue Coverage (aggregate) ---")
    for i in range(n):
        marker = " ← LEAST COVERED" if i == min_cov_r else ""
        print(f"  r={i}: covered in {total_cov[i]:>8} fibers{marker}")

    # D=0 runner profiles: most common
    from collections import Counter
    all_profiles = []
    for r in all_results:
        all_profiles.extend(r["dz_runner_profiles"])
    if all_profiles:
        profile_counts = Counter(all_profiles)
        print(f"\n--- D=0 Runner Coverage Profiles (top 5) ---")
        for prof, cnt in profile_counts.most_common(5):
            gs = tuple(gcd(e, n) for e in prof)
            print(f"  runners={prof}, g_e={gs}, count={cnt}")


def print_sample_coset_rotation(results: dict, n: int):
    """Show coset rotation for one non-unit runner."""
    for e in results["e_non"]:
        g = gcd(e, n)
        if 1 < g < n:
            cv = results["coset_visits"][e]
            if cv:
                print(f"\n  Coset rotation for e={e} (g={g}, H_g={sorted(subgroup(g,n))}):")
                total = sum(cv.values())
                for rep, cnt in sorted(cv.items()):
                    coset = frozenset((rep + k * (n // g)) % n for k in range(g))
                    print(f"    coset={sorted(coset)} (rep={rep}): visits={cnt}/{total}")
                return


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def run_for_n(n: int, max_speed_mult: int = 4, max_L: int = 100000):
    print(f"\n{'#'*60}")
    print(f"# n = {n}")
    print(f"{'#'*60}")

    max_e = max_speed_mult * n
    all_results = []

    for combo in gen_tuples(n, max_e, max_L):
        r = analyze_tuple(n, combo)
        all_results.append(r)

    if not all_results:
        print(f"  No admissible tuples found for n={n}.")
        return

    print_summary(all_results, n)

    # Show one sample tuple detail
    sample = all_results[0]
    print(f"\n--- Sample Tuple: n={n}, E={sample['e_non']}, L={sample['L']}, M={sample['M']} ---")
    print(f"  B_safe={sample['safe_count']}, obst={sample['obstructed_count']}, max_run={sample['max_run']}")
    print(f"  First obstruction: j={sample['first_obst_j']}, b={sample['first_obst_b']}")
    print_sample_coset_rotation(sample, n)

    # Show a specific D=0 fiber if it exists
    if sample["first_obst_b"] is not None:
        b_dz = sample["first_obst_b"]
        L = sample["L"]
        print(f"\n  Detail at first D=0 fiber b={b_dz}:")
        for e in sample["e_non"]:
            g = gcd(e, n)
            t_e = floor_state(e, b_dz, L)
            B = bad_set_canonical(e, b_dz, L, n)
            print(f"    e={e:3d} g={g} t_e={t_e:4d} B_e(b)={sorted(B)}")
        U_full = set()
        for e in sample["e_non"]:
            U_full |= bad_set_canonical(e, b_dz, L, n)
        print(f"    U(b) = {sorted(U_full)}   D(b) = {n - len(U_full)}")

    return all_results


def main():
    EVEN_N  = [6, 8, 10, 12]
    ODD_N   = [9, 15]

    all_n_results = {}

    for n in EVEN_N:
        res = run_for_n(n, max_speed_mult=3, max_L=50000)
        all_n_results[n] = res

    for n in ODD_N:
        res = run_for_n(n, max_speed_mult=3, max_L=50000)
        all_n_results[n] = res

    # Global summary
    print(f"\n{'='*60}")
    print("GLOBAL SUMMARY")
    print(f"{'='*60}")
    all_dct_viol = 0
    all_d1_viol = 0
    for n, res in all_n_results.items():
        if res is None:
            continue
        dv = sum(r["dct_match_violations"] for r in res)
        d1 = sum(r["d1_nonunit_violations"] + r["d1_size_violations"] + r["d1_coset_violations"]
                 for r in res)
        all_dct_viol += dv
        all_d1_viol += d1
        b_lt = sum(1 for r in res if r["safe_count"] < n and r["M"] >= n)
        lbl_viol = sum(1 for r in res if r["first_obst_j"] is not None and r["first_obst_j"] < n)
        print(f"  n={n:2d}: DCT_viol={dv:4d}  D1_viol={d1:4d}  "
              f"Bsafe<n (M≥n)={b_lt:4d}  LBL_viol={lbl_viol:4d}")

    print(f"\n  Total DCT violations across all n: {all_dct_viol}  (expect 0)")
    print(f"  Total D1 violations across all n:  {all_d1_viol}   (expect 0)")


if __name__ == "__main__":
    main()
