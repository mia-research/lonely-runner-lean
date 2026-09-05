"""
lrc_gap_investigation_v2.py
============================
Investigate WHY the small-parameter enumeration cases in Appendix A.4 and A.5
satisfy x_0 >= phi(n).  For each hard case, classify every safe fibre by mechanism:

  SOLE_COVER   : fibre in I_d = [L/n, L/(n-1))         (residue r_d = -d^-1 exposed)
  DUAL_SOLE    : fibre in J   = [(n-2)L/(n-1),(n-1)L/n] (residue s_d = d^-1-1 exposed)
  FLOOR_RESET  : fibre is exactly a floor-reset event b = m*L/e_u for some unit e_u
  OTHER        : none of the above — unclassified, needs further investigation

Usage:
  python3 lrc_gap_investigation_v2.py          # both A.4 and A.5
  python3 lrc_gap_investigation_v2.py --a5     # A.5 only
  python3 lrc_gap_investigation_v2.py --a4     # A.4 only
  python3 lrc_gap_investigation_v2.py -v       # verbose (print every extremal case)
"""

import sys
import math
import itertools
from fractions import Fraction
from collections import defaultdict


# ---------------------------------------------------------------------------
# Arithmetic helpers
# ---------------------------------------------------------------------------

def euler_phi(n):
    result, temp = n, n
    p = 2
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            result -= result // p
        p += 1
    if temp > 1:
        result -= result // temp
    return result


def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x


def mod_inv(a, n):
    g, x, _ = extended_gcd(a % n, n)
    assert g == 1, f"gcd({a},{n})={g} != 1"
    return x % n


def lcm_list(lst):
    r = 1
    for x in lst:
        r = math.lcm(r, x)
    return r


def is_prime(n):
    if n < 2: return False
    for p in range(2, int(n**0.5) + 1):
        if n % p == 0: return False
    return True


# ---------------------------------------------------------------------------
# Core: bad set
# ---------------------------------------------------------------------------

def bad_set(e, t, n):
    """bad(e,t,n) = Sol(e,-t,n) ∪ Sol(e,-(t+1),n) as a Python set."""
    g = math.gcd(e, n)
    result = set()
    for j_neg in (t, t + 1):          # we want Sol(e, -j_neg, n)
        j = (-j_neg) % n
        if j % g == 0:
            eg, ng, jg = e // g, n // g, j // g
            r0 = (jg * mod_inv(eg, ng)) % ng
            for k in range(g):
                result.add(r0 + k * ng)
    return result


# ---------------------------------------------------------------------------
# Core: compute safe fibres with mechanism classification
# ---------------------------------------------------------------------------

def compute_safe_fibres(E_non, n, dropped_unit):
    """
    Returns (x0, safe_list, L) where safe_list is a list of
    (b, mechanism_label, detail_string) for every safe fibre b in B_div.
    """
    d = dropped_unit
    L_non = lcm_list(E_non)
    L = L_non if L_non % n == 0 else L_non * n
    # Full runner set: E_non + divisible runner n
    E_full = list(E_non) + [n]
    N = n * L

    step = L // n              # = L/n (integer)
    B_div = [step * k for k in range(1, n)]   # b = L/n, 2L/n, ..., (n-1)L/n

    # Interval bounds (rational to avoid float issues)
    I_lo = Fraction(L, n)
    I_hi = Fraction(L, n - 1)
    J_lo = Fraction((n - 2) * L, n - 1)
    J_hi = Fraction((n - 1) * L, n)

    d_inv = mod_inv(d, n)
    r_d = (-d_inv) % n           # residue exposed on I_d
    s_d = (d_inv - 1) % n       # residue exposed on J

    # Pre-compute floor-reset lookup: {b_reset_as_int: (e_u, m)} for exact hits
    reset_map = {}
    for e_u in E_non:
        if math.gcd(e_u, n) != 1:
            continue
        for m in range(1, e_u):
            num = m * L
            if num % e_u == 0:
                reset_map[num // e_u] = (e_u, m)

    safe_list = []
    lo, hi = L, (n - 1) * L

    for b in B_div:
        if not all(lo <= (e * b) % N <= hi for e in E_full):
            continue

        bf = Fraction(b)
        if I_lo <= bf < I_hi:
            safe_list.append((b, "SOLE_COVER",
                f"r_d={r_d}(=-{d}^-1 mod {n}); d_inv={d_inv}"))
        elif J_lo <= bf <= J_hi:
            safe_list.append((b, "DUAL_SOLE",
                f"s_d={s_d}(={d_inv}-1 mod {n}); d_inv={d_inv}"))
        elif b in reset_map:
            e_u, m = reset_map[b]
            eu_inv = mod_inv(e_u, n)
            dep = (-(m - 1) * eu_inv) % n
            safe_list.append((b, "FLOOR_RESET",
                f"e_u={e_u}, m={m}, dep_residue={dep}, "
                f"floor {m-1}→{m} at b={b}=L/{e_u//math.gcd(m*L//e_u,1) if False else e_u//1}*{m}"))
        else:
            # Describe the actual coverage gap
            covered = set()
            for e in E_non:
                t = (e * b) // L
                covered |= bad_set(e, t, n)
            uncovered = sorted(set(range(n)) - covered)
            floors = {e: (e * b) // L for e in E_non}
            safe_list.append((b, "OTHER",
                f"uncovered={uncovered}, floors={floors}"))

    return len(safe_list), safe_list, L


# ---------------------------------------------------------------------------
# A.5: composite n <= 12, small L
# ---------------------------------------------------------------------------

def run_A5(verbose=False):
    print("\n" + "="*72)
    print("A.5 INVESTIGATION  (composite n ≤ 12, new threshold L < n(n-1)(φ/2+1))")
    print("="*72)

    composite_ns = [n for n in range(4, 13) if not is_prime(n)]
    grand_extremal = []

    for n in composite_ns:
        phi_n = euler_phi(n)
        L_thresh = n * (n - 1) * (phi_n // 2 + 1)
        all_units = [a for a in range(1, n) if math.gcd(a, n) == 1]
        all_res   = list(range(1, n))

        print(f"\n── n={n}  φ(n)={phi_n}  threshold L < {L_thresh} ──")

        results, extremal = [], []

        for d in all_units:
            remaining = [a for a in all_res if a != d]
            # Drop one more element (second drop = drop2)
            for drop2 in remaining:
                E_non = [a for a in remaining if a != drop2]
                if len(E_non) != n - 3:
                    continue

                L_non = lcm_list(E_non)
                L = L_non if L_non % n == 0 else L_non * n

                if L >= L_thresh or L <= 2 * n:
                    continue

                x0, sf, L_act = compute_safe_fibres(E_non, n, d)
                rec = dict(n=n, L=L_act, d=d, drop2=drop2,
                           E_non=sorted(E_non), x0=x0, phi_n=phi_n,
                           safe_fibres=sf)
                results.append(rec)

                if x0 < phi_n:
                    print(f"  *** FAILURE x0={x0} < phi={phi_n}  "
                          f"d={d} drop2={drop2} E={sorted(E_non)} L={L_act}")
                elif x0 == phi_n:
                    extremal.append(rec)

        grand_extremal.extend(extremal)

        if results:
            x0s = [r['x0'] for r in results]
            fails = sum(1 for x in x0s if x < phi_n)
            print(f"  cases={len(results)}  failures={fails}  "
                  f"x0∈[{min(x0s)},{max(x0s)}]  extremal={len(extremal)}")
        else:
            print("  (no cases in range)")

        if extremal:
            _print_mechanism_summary(extremal, f"A.5 n={n}", verbose=verbose)

    if grand_extremal:
        _print_mechanism_summary(grand_extremal, "A.5 ALL COMPOSITE", verbose=False)


# ---------------------------------------------------------------------------
# A.4: prime n, small M
# ---------------------------------------------------------------------------

def run_A4(verbose=False):
    print("\n" + "="*72)
    print("A.4 INVESTIGATION  (prime n ≤ 30, small M < M_0)")
    print("="*72)

    prime_ns = [n for n in range(5, 31) if is_prime(n)]
    grand_extremal = []

    for n in prime_ns:
        phi_n = n - 1
        all_res = list(range(1, n))

        print(f"\n── n={n} (prime)  φ(n)={phi_n} ──")

        results, extremal = [], []
        has_any_small_M = False

        for d1, d2 in itertools.combinations(all_res, 2):
            E_non = [a for a in all_res if a != d1 and a != d2]
            L_0 = lcm_list(E_non)
            M_0 = math.ceil(n * n * (n - 1) / (L_0 * (n - 2)))

            if M_0 <= 1:
                continue  # analytic branch covers everything
            has_any_small_M = True

            for M in range(1, M_0):
                L = L_0 * M
                # For each choice of "dropped unit" (here both d1, d2 are units
                # since n is prime), run classification for each.
                for d in (d1, d2):
                    x0, sf, L_act = compute_safe_fibres(E_non, n, d)
                    rec = dict(n=n, L=L_act, L_0=L_0, M=M, M_0=M_0,
                               d=d, drop_other=d2 if d==d1 else d1,
                               E_non=sorted(E_non), x0=x0, phi_n=phi_n,
                               safe_fibres=sf)
                    results.append(rec)

                    if x0 < phi_n:
                        print(f"  *** FAILURE x0={x0} < phi={phi_n}  "
                              f"d={d} E={sorted(E_non)} L={L_act} M={M}")
                    elif x0 == phi_n:
                        extremal.append(rec)

        grand_extremal.extend(extremal)

        if not has_any_small_M:
            print(f"  M_0=1 for all configurations — fully analytic, no enumeration needed.")
        elif results:
            x0s = [r['x0'] for r in results]
            fails = sum(1 for x in x0s if x < phi_n)
            M0s = sorted(set(r['M_0'] for r in results))
            print(f"  cases={len(results)}  failures={fails}  "
                  f"x0∈[{min(x0s)},{max(x0s)}]  extremal={len(extremal)}  M_0 values={M0s}")
        else:
            print("  (no small-M cases after filtering)")

        if extremal:
            _print_mechanism_summary(extremal, f"A.4 n={n}", verbose=verbose)

    if grand_extremal:
        _print_mechanism_summary(grand_extremal, "A.4 ALL PRIME", verbose=False)


# ---------------------------------------------------------------------------
# Summary printer
# ---------------------------------------------------------------------------

def _print_mechanism_summary(cases, label, verbose=False):
    print(f"\n  ┌─ {label}: {len(cases)} extremal cases ─┐")

    mech_tally = defaultdict(int)
    sole_only = dual_only = reset_only = mixed = has_other = 0

    for c in cases:
        mechs = {m for (_, m, _) in c['safe_fibres']}
        for m in mechs:
            mech_tally[m] += 1
        if mechs == {'SOLE_COVER'}:    sole_only  += 1
        elif mechs == {'DUAL_SOLE'}:   dual_only  += 1
        elif mechs == {'FLOOR_RESET'}: reset_only += 1
        elif 'OTHER' in mechs:         has_other  += 1
        else:                          mixed      += 1

    for mech, cnt in sorted(mech_tally.items()):
        print(f"  │  {mech:14s} present in {cnt}/{len(cases)} cases")
    print(f"  │  pure breakdown: sole={sole_only} dual={dual_only} "
          f"reset={reset_only} mixed={mixed} has_OTHER={has_other}")

    if has_other > 0:
        print(f"\n  *** UNCLASSIFIED 'OTHER' SAFE FIBRES — NEEDS INVESTIGATION ***")
        for c in cases:
            others = [(b, det) for (b, m, det) in c['safe_fibres'] if m == 'OTHER']
            if others:
                print(f"    n={c['n']} L={c['L']} d={c['d']} E={c['E_non']}")
                for b, det in others:
                    print(f"      b={b}: {det}")

    if verbose:
        print(f"\n  Detailed extremal cases:")
        for c in cases:
            tag = "A4" if 'M' in c else "A5"
            if 'M' in c:
                print(f"    [{tag}] n={c['n']} L={c['L']} M={c['M']}/M0={c['M_0']} "
                      f"d={c['d']} E={c['E_non']}  x0={c['x0']}")
            else:
                print(f"    [{tag}] n={c['n']} L={c['L']} d={c['d']} "
                      f"drop2={c['drop2']} E={c['E_non']}  x0={c['x0']}")
            for (b, mech, det) in c['safe_fibres']:
                print(f"      b={b:8d}  {mech:14s}  {det}")

    print(f"  └{'─'*50}┘")


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    verbose = "-v" in sys.argv or "--verbose" in sys.argv
    do_a4   = "--a4" in sys.argv
    do_a5   = "--a5" in sys.argv
    if not do_a4 and not do_a5:
        do_a4 = do_a5 = True

    if do_a5:
        run_A5(verbose=verbose)
    if do_a4:
        run_A4(verbose=verbose)
