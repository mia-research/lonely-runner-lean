#!/usr/bin/env python3
"""
lrc_uforce_exception_hunter_v1.py
===================================
Exception-hunting analysis for Theorem 8.3 Sub-case (i) — U-FORCE condition.

Exact integer arithmetic throughout (no floating point for floor operations).

Task: enumerate every z=0 event for each unit runner in the U-FORCE scenario,
classify as isolated or non-isolated, run the relay invariant on every z=0 fibre,
and produce Tables 1 / 2 / 3 per the research prompt.

Key formulas (L-independent floor state):
  z=0 event of unit e_u: b = m * L / e_u   (m = 1 .. e_u-1)
  Floor state of e_v at that fibre:  f_v = (e_v * m) // e_u   [exact int division]
  Departing residue:  r_dep = (-(m-1) * modinv(e_u, n)) % n
  Isolation: no e_v (v ≠ u) has r_dep in bad_set(e_v, f_v, n)
  bad_set(e, t, n) = Sol(e, -t, n) ∪ Sol(e, -(t+1), n)
"""

from math import gcd
from fractions import Fraction
from collections import Counter, defaultdict


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


def non_units_mod_n(n):
    return [e for e in range(2, n) if gcd(e, n) > 1]


def bad_set(e, t, n):
    """
    bad(e, t, n) = Sol(e, -t, n) ∪ Sol(e, -(t+1), n)
    Sol(e, j, n) = {r : e·r ≡ j (mod n)}
    Exact: uses modular inverse; handles non-unit e via gcd structure.
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


def distinct_prime_factors(n):
    factors, temp, d = set(), n, 2
    while d * d <= temp:
        if temp % d == 0:
            factors.add(d)
            while temp % d == 0:
                temp //= d
        d += 1
    if temp > 1:
        factors.add(temp)
    return factors


# ── core analysis for one (n, L) pair ──────────────────────────────────────

def analyze_n_L(n, L, verbose=False):
    """
    Returns (table1_row, table2_rows) for the U-FORCE scenario at (n, L).
    U-FORCE: E_non = all φ(n) unit speeds; two smallest non-units dropped.
    """
    phi_n = euler_phi(n)
    units = units_mod_n(n)
    non_units = non_units_mod_n(n)
    active_units = [e for e in units if e > 1]  # units with z=0 events

    # U-FORCE: all units active
    E_non = units[:]
    dropped = non_units[:2] if len(non_units) >= 2 else list(non_units)

    # Theoretical bound = sum_{e_u unit, e_u≥2} (e_u - 1) = φ(n)(n-2)/2
    theoretical_bound = sum(e - 1 for e in active_units)

    # B_div = [n, L-n]
    b_lo, b_hi = n, L - n
    if b_lo > b_hi:
        return None, []  # L too small for any safe fibres

    # Verify divisibility
    for e_u in active_units:
        if L % e_u != 0:
            raise ValueError(f"L={L} not divisible by e_u={e_u} (need L | lcm(units))")

    # Precompute modular inverses of all active units
    inv_eu = {e: modinv(e, n) for e in active_units}

    # ── enumerate all z=0 events in B_div ──
    z0_events = []  # (b, e_u, m)
    for e_u in active_units:
        for m in range(1, e_u):
            b = m * L // e_u  # exact integer since e_u | L
            if b_lo <= b <= b_hi:
                z0_events.append((b, e_u, m))

    total_z0 = len(z0_events)
    isolated_count = 0
    table2_rows = []
    safe_fibres = set()   # fibres confirmed safe via relay invariant

    for (b, e_u, m) in z0_events:
        r_dep = (-(m - 1) * inv_eu[e_u]) % n

        # ── isolation check ──
        # Floor state of e_v at this fibre is (e_v * m) // e_u  [L-independent]
        interfering = []
        for e_v in E_non:
            if e_v == e_u:
                continue
            f_v = (e_v * m) // e_u
            if r_dep in bad_set(e_v, f_v, n):
                interfering.append((e_v, f_v))

        if not interfering:
            isolated_count += 1
        else:
            # position_in_Bdiv = (b - n) / (L - 2n) as exact fraction
            pos = Fraction(b - n, L - 2 * n) if L > 2 * n else Fraction(0)
            for (e_v, f_v) in interfering:
                table2_rows.append({
                    'n': n,
                    'L': L,
                    'e_u': e_u,
                    'm': m,
                    'b': b,
                    'r': r_dep,
                    'e_v': e_v,
                    'floor_ev': f_v,
                    'gcd_eu_ev': gcd(e_u, e_v),
                    'gcd_eu_n': gcd(e_u, n),
                    'gcd_ev_n': gcd(e_v, n),
                    'm_mod_eu': m % e_u,
                    'm_mod_ev': m % e_v,
                    'position': pos,
                })

        # ── relay invariant: is the fibre safe at all? ──
        # Compute union of bad sets for all runners at this fibre
        union_bad = set()
        for e_v in E_non:
            if e_v == e_u:
                # Transitioning runner: conservatively include both floor states
                union_bad |= bad_set(e_u, m - 1, n)
                union_bad |= bad_set(e_u, m, n)
            else:
                f_v = (e_v * m) // e_u
                union_bad |= bad_set(e_v, f_v, n)
        miss = set(range(n)) - union_bad
        if miss:
            safe_fibres.add(b)

    B_safe = len(safe_fibres)
    non_isolated = total_z0 - isolated_count
    isolation_rate = (Fraction(isolated_count, total_z0)
                      if total_z0 > 0 else Fraction(1))
    ratio = (Fraction(B_safe, theoretical_bound)
             if theoretical_bound > 0 else None)
    passes = (B_safe >= theoretical_bound)

    t1 = {
        'n': n, 'L': L, 'phi_n': phi_n,
        'bound': theoretical_bound,
        'total_z0': total_z0,
        'isolated': isolated_count,
        'non_isolated': non_isolated,
        'isolation_rate': isolation_rate,
        'B_safe': B_safe,
        'ratio': ratio,
        'PASS': passes,
        'dropped': dropped,
    }
    return t1, table2_rows


# ── main ────────────────────────────────────────────────────────────────────

def main():
    n_values_raw = [6, 10, 12, 15, 30, 42]
    k_values = [1, 5, 10, 50, 100]

    # Keep only n with ≥ 2 distinct prime factors (Sub-case (i) scope)
    n_values = [n for n in n_values_raw
                if len(distinct_prime_factors(n)) >= 2]

    print("=" * 80)
    print("LRC U-FORCE EXCEPTION HUNTER v1")
    print("Theorem 8.3 Sub-case (i): prove B_safe ≥ φ(n)(n-2)/2 via z=0 isolation")
    print("=" * 80)
    print()

    all_t1 = []
    all_t2 = []

    for n in n_values:
        units = units_mod_n(n)
        active_units = [e for e in units if e > 1]
        lcm_u = lcm_list(active_units) if active_units else 1
        phi_n = euler_phi(n)
        bound = sum(e - 1 for e in active_units)
        dropped = non_units_mod_n(n)[:2]

        print(f"n={n}: phi={phi_n}, units={units}")
        print(f"  active_units (e>1): {active_units}")
        print(f"  lcm(active_units) = {lcm_u}")
        print(f"  bound phi(n)(n-2)/2 = {bound}")
        print(f"  dropped (non-units for U-FORCE): {dropped}")
        print()

        for k in k_values:
            L = k * lcm_u
            if L <= 2 * n:
                print(f"  k={k:3d}, L={L:>15}: B_div empty — skip")
                continue
            t1, t2 = analyze_n_L(n, L)
            if t1 is None:
                print(f"  k={k:3d}, L={L:>15}: B_div empty — skip")
                continue
            all_t1.append(t1)
            all_t2.extend(t2)

            iso_pct = f"{float(t1['isolation_rate']) * 100:.1f}%"
            ratio_s = (f"{float(t1['ratio']):.4f}"
                       if t1['ratio'] is not None else "N/A")
            pass_s = "PASS" if t1['PASS'] else "FAIL !!!"
            print(f"  k={k:3d}, L={L:>15}: "
                  f"z0={t1['total_z0']:3d}  "
                  f"isolated={t1['isolated']:3d}  "
                  f"non-iso={t1['non_isolated']:3d} ({iso_pct})  "
                  f"B_safe={t1['B_safe']:3d}/{t1['bound']}  "
                  f"ratio={ratio_s}  [{pass_s}]")
        print()

    # ── TABLE 1 ──────────────────────────────────────────────────────────────
    sep = "=" * 115
    print(sep)
    print("TABLE 1 — AGGREGATE COUNTS")
    print(sep)
    hdr = (f"{'n':>4}  {'L':>16}  {'phi':>4}  {'bound':>5}  "
           f"{'z0':>5}  {'iso':>5}  {'non-iso':>7}  "
           f"{'iso_rate':>9}  {'B_safe':>6}  {'ratio':>7}  {'PASS':>5}")
    print(hdr)
    print("-" * 115)
    for r in all_t1:
        ratio_s = (f"{float(r['ratio']):.4f}"
                   if r['ratio'] is not None else "N/A ")
        rate_s = f"{float(r['isolation_rate']):.4f}"
        pass_s = "YES" if r['PASS'] else "NO!"
        print(f"{r['n']:>4}  {r['L']:>16}  {r['phi_n']:>4}  {r['bound']:>5}  "
              f"{r['total_z0']:>5}  {r['isolated']:>5}  {r['non_isolated']:>7}  "
              f"{rate_s:>9}  {r['B_safe']:>6}  {ratio_s:>7}  {pass_s:>5}")

    # ── TABLE 2 ──────────────────────────────────────────────────────────────
    print()
    print(sep)
    print("TABLE 2 — NON-ISOLATED EVENT ANATOMY (every non-isolated z=0 event)")
    print(sep)
    if not all_t2:
        print("  *** EMPTY — All z=0 events are isolated across all tested (n, L). ***")
        print("  → Route D (lower band isolation) likely closes the gap trivially.")
        print("  → Try small k=1,2,3 or smaller n to find any non-isolated events.")
    else:
        hdr2 = (f"{'n':>4}  {'L':>10}  {'e_u':>4}  {'m':>4}  {'b':>14}  "
                f"{'r':>3}  {'e_v':>4}  {'f(ev)':>6}  "
                f"{'g(u,v)':>7}  {'g(u,n)':>7}  {'g(v,n)':>7}  "
                f"{'m%eu':>5}  {'m%ev':>5}  {'pos_Bdiv':>9}")
        print(hdr2)
        print("-" * 115)
        for r in all_t2:
            pos_s = f"{float(r['position']):.5f}"
            print(f"{r['n']:>4}  {r['L']:>10}  {r['e_u']:>4}  {r['m']:>4}  "
                  f"{r['b']:>14}  {r['r']:>3}  {r['e_v']:>4}  {r['floor_ev']:>6}  "
                  f"{r['gcd_eu_ev']:>7}  {r['gcd_eu_n']:>7}  {r['gcd_ev_n']:>7}  "
                  f"{r['m_mod_eu']:>5}  {r['m_mod_ev']:>5}  {pos_s:>9}")

    # ── TABLE 3 ──────────────────────────────────────────────────────────────
    print()
    print(sep)
    print("TABLE 3 — PATTERN SUMMARY ACROSS NON-ISOLATED EVENTS")
    print(sep)

    if not all_t2:
        print("  No non-isolated events → no pattern to analyze.")
        print()
        print("  CRITICAL QUESTION ANSWER: (A) BOUNDED — count is 0, constant in L.")
    else:
        total_ni = len(all_t2)
        print(f"  Total non-isolated event rows: {total_ni}")

        print()
        print("[A] Floor state of interfering runner e_v:")
        fs_dist = Counter(r['floor_ev'] for r in all_t2)
        for fs, cnt in sorted(fs_dist.items()):
            marker = "  *** floor_state=0 (Sole Cover baseline)" if fs == 0 else ""
            print(f"  floor_state = {fs:3d}: {cnt:5d} ({100*cnt/total_ni:5.1f}%){marker}")

        print()
        print("[B] gcd(e_u, e_v) distribution:")
        gcd_dist = Counter(r['gcd_eu_ev'] for r in all_t2)
        for g_val, cnt in sorted(gcd_dist.items()):
            print(f"  gcd = {g_val}: {cnt:5d} ({100*cnt/total_ni:5.1f}%)")

        print()
        print("[C] m mod e_u distribution:")
        print("  (algebraic criterion: non-isolated iff (e_u/gcd(e_u,e_v)) | (m-1))")
        meu_dist = Counter(r['m_mod_eu'] for r in all_t2)
        for v, cnt in sorted(meu_dist.items()):
            print(f"  m mod e_u = {v}: {cnt:5d} ({100*cnt/total_ni:5.1f}%)")

        print()
        print("[D] m mod e_v distribution:")
        mev_dist = Counter(r['m_mod_ev'] for r in all_t2)
        for v, cnt in sorted(mev_dist.items()):
            print(f"  m mod e_v = {v}: {cnt:5d} ({100*cnt/total_ni:5.1f}%)")

        # Scaling analysis
        print()
        print("[E] Scaling of non-isolated count vs k (by n):")
        by_n_ni = defaultdict(list)   # n -> [(k, non_isolated, total_z0, isolated)]
        for r in all_t1:
            n_val = r['n']
            units_v = units_mod_n(n_val)
            active_v = [e for e in units_v if e > 1]
            lcm_v = lcm_list(active_v) if active_v else 1
            k_val = r['L'] // lcm_v if lcm_v and r['L'] % lcm_v == 0 else None
            by_n_ni[n_val].append((k_val, r['non_isolated'], r['total_z0'], r['isolated']))

        for n_val in sorted(by_n_ni.keys()):
            entries = sorted(by_n_ni[n_val], key=lambda x: (x[0] is None, x[0]))
            ni_vals = [x[1] for x in entries]
            k_vals = [x[0] for x in entries]
            print(f"  n={n_val}:")
            for (kv, ni, tot, iso) in entries:
                print(f"    k={str(kv):>4}: non_iso={ni:4d}  total_z0={tot:4d}  isolated={iso:4d}")
            # Classify scaling
            if len(set(ni_vals)) == 1:
                verdict = f"(A) BOUNDED (constant={ni_vals[0]})"
            else:
                # Check proportionality to k
                valid = [(kv, ni) for kv, ni in zip(k_vals, ni_vals)
                         if kv is not None and ni > 0]
                if len(valid) >= 2:
                    rates = [ni / kv for kv, ni in valid]
                    rel_var = (max(rates) - min(rates)) / max(rates)
                    if rel_var < 0.01:
                        verdict = "(C) PROPORTIONAL TO L"
                    else:
                        verdict = "(B) SUBLINEAR"
                else:
                    verdict = "UNDETERMINED"
            print(f"    → Scaling verdict: {verdict}")
            print()

        # Summary of relay invariant (every non-isolated fibre still safe?)
        print()
        print("[F] Relay invariant summary for non-isolated events:")
        print("    (B_safe counts fibres safe via ANY uncovered residue, not just r_dep)")
        by_n_pass = defaultdict(lambda: {'z0': 0, 'isolated': 0, 'B_safe': 0, 'bound': 0})
        for r in all_t1:
            n_val = r['n']
            by_n_pass[n_val]['z0'] += r['total_z0']
            by_n_pass[n_val]['isolated'] += r['isolated']
            by_n_pass[n_val]['B_safe'] = max(by_n_pass[n_val]['B_safe'], r['B_safe'])
            by_n_pass[n_val]['bound'] = r['bound']
        # This isn't quite right for summing across k — just report per-row
        pass_count = sum(1 for r in all_t1 if r['PASS'])
        fail_count = sum(1 for r in all_t1 if not r['PASS'])
        print(f"  Rows with PASS (B_safe >= bound): {pass_count}/{len(all_t1)}")
        if fail_count:
            print(f"  FAILURES (B_safe < bound): {fail_count}")
            for r in all_t1:
                if not r['PASS']:
                    print(f"    n={r['n']}, L={r['L']}: B_safe={r['B_safe']} < bound={r['bound']}")
        else:
            print("  All rows PASS. B_safe >= phi(n)(n-2)/2 confirmed for all tested (n,L).")

    # ── CRITICAL QUESTION ANSWER ──────────────────────────────────────────────
    print()
    print("=" * 80)
    print("CRITICAL QUESTION: As L → ∞, does the non-isolated count:")
    print("  (A) Stay bounded by a constant (independent of L)?")
    print("  (B) Grow sublinearly in L?")
    print("  (C) Grow proportionally to L?")
    print()
    if not all_t2:
        print("ANSWER: (A) BOUNDED — non-isolated count = 0 for all tested L.")
        print("→ Route D (lower band): all z=0 events isolated trivially.")
    else:
        # Look at variation across k for each n
        by_n_ni2 = defaultdict(list)
        for r in all_t1:
            n_val = r['n']
            units_v = units_mod_n(n_val)
            active_v = [e for e in units_v if e > 1]
            lcm_v = lcm_list(active_v) if active_v else 1
            k_val = r['L'] // lcm_v if lcm_v and r['L'] % lcm_v == 0 else None
            if k_val is not None:
                by_n_ni2[n_val].append((k_val, r['non_isolated']))

        verdicts = set()
        for n_val, entries in by_n_ni2.items():
            ni_vals = [ni for _, ni in entries]
            if len(set(ni_vals)) <= 1:
                verdicts.add('A')
            else:
                valid = [(k, ni) for k, ni in entries if ni > 0]
                if len(valid) >= 2:
                    rates = [ni / k for k, ni in valid]
                    rel_var = (max(rates) - min(rates)) / max(rates)
                    verdicts.add('C' if rel_var < 0.01 else 'B')

        verdict_str = " and ".join(sorted(verdicts))
        print(f"ANSWER: ({verdict_str})")
        if verdicts == {'A'}:
            print("→ Non-isolated count is CONSTANT in L for all tested n.")
            print("→ Since total z=0 events also constant, and B_safe ≥ total_z0")
            print("  (relay invariant covers non-isolated fibres too), the bound holds")
            print("  with ratio B_safe / bound ≥ 1 for sufficiently large L.")
            print("→ Best analytic route: Route D or Route C (count is O(n²), not O(L)).")
        elif 'C' in verdicts:
            print("→ Non-isolated count grows proportionally to L.")
            print("→ But so does total z=0 count, so isolation RATE is constant.")
            print("→ Route A (floor-state equidistribution) is the mechanism.")

    print()
    print("Script complete.")


if __name__ == "__main__":
    main()
