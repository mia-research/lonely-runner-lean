"""
Structure check for Conjecture 5.2-SR-H attack.

Claims to verify on the 34 SR-failure cases (and synthetic LRC-shape inputs):
  (L1)  For w in W_1 with gcd(w,n)=1, bad_k(w,c) = {0, -w^{-1} mod n}
        IDENTICALLY across all c in (Z/n)^*.
  (L2)  For w in W_1 with gcd(w,n)=d>1, bad_k(w,c) is either empty or a coset
        of the order-d subgroup <n/d> in Z/n, with exactly d elements.
  (L3)  For w in W_1 with gcd(w,n)=1 and any c, bad_k(w,c) is disjoint from
        S_n := {k in {1,..,n-1}: 1 < gcd(k,n) < n}  (the non-zero non-units).

Also tabulate:
  - LRC-shape: |W_1| + |W_2| = n - 1
  - SR-failure substratum: |W_2| >= 1, so |W_1| <= n-2

If L1/L2/L3 hold across all data, the n-prime case is settled (Case 1)
and the analytic task narrows to: for composite n, find unit c with non-unit
safe k. Validates the strategic split.
"""
import csv
import math

CSV = "/Users/trentpalelei/Desktop/Math Ex/reports/phase6_residual_arithmetic.csv"


def parse_speeds(s):
    return [int(x) for x in s.split("-")]


def norm_int(num, den):
    r = num % den
    return min(r, den - r)


def bad_k_set(n, w, c):
    """Return set of k in {0,...,n-1} with ||w(nk+c)/n^2|| < 1/n."""
    n2 = n * n
    return {k for k in range(n) if norm_int(w * (n * k + c), n2) * n < n2}


def check_L1_L2_L3(n, W1):
    """Verify L1', L2, L3 on a single configuration (n, W1).

    L1' (corrected): For gcd(w,n)=1, bad_k(w,c) is a PAIR {k_1, k_2}
                     with k_2 - k_1 = -w^{-1} mod n (i.e., gap is fixed).
                     Both elements depend on c via beta = floor(wc / n) mod n.
                     Specifically k_1 = -beta * w^{-1}, k_2 = -(beta+1) * w^{-1}.
    """
    units_c = [c for c in range(1, n) if math.gcd(c, n) == 1]
    S_n = {k for k in range(1, n) if 1 < math.gcd(k, n) < n}

    results = {'L1_ok': True, 'L2_ok': True, 'L3_ok': True,
               'L1_violations': [], 'L2_violations': [], 'L3_violations': []}

    for w in W1:
        d = math.gcd(w, n)
        n1 = n // d
        bad_per_c = {c: bad_k_set(n, w, c) for c in units_c}

        if d == 1:
            # L1' (corrected): bad-k pair {k_1, k_1 - w^{-1}} with k_1 depending on c
            w_inv = pow(w, -1, n)
            for c in units_c:
                bad = bad_per_c[c]
                if len(bad) != 2:
                    results['L1_ok'] = False
                    results['L1_violations'].append((w, c, bad, 'size != 2'))
                    continue
                bad_list = sorted(bad)
                gap = (bad_list[1] - bad_list[0]) % n
                # gap should be either -w^{-1} mod n or w^{-1} mod n (since we sorted)
                if gap != ((-w_inv) % n) and gap != (w_inv % n):
                    results['L1_ok'] = False
                    results['L1_violations'].append((w, c, bad, f'gap {gap} != +/- {w_inv}'))
                # Also predicted by formula k_1 = -beta * w^{-1}, k_2 = -(beta+1) * w^{-1}
                beta = (w * c % (n * n)) // n
                pred_k1 = (-beta * w_inv) % n
                pred_k2 = (-(beta + 1) * w_inv) % n
                if bad != {pred_k1, pred_k2}:
                    results['L1_ok'] = False
                    results['L1_violations'].append((w, c, bad, {pred_k1, pred_k2}))
            # L3: bad-k pairs are in (Z/n)? Check: are they always in {0} ∪ (Z/n)^*?
            for c in units_c:
                bad = bad_per_c[c]
                if bad & S_n:
                    results['L3_ok'] = False
                    results['L3_violations'].append((w, c, bad & S_n))
        else:
            # L2: bad_k(w,c) is empty or a coset of <n/d>, of size d
            subgroup = {(i * n1) % n for i in range(d)}
            for c in units_c:
                bad = bad_per_c[c]
                if len(bad) == 0:
                    continue
                if len(bad) != d:
                    results['L2_ok'] = False
                    results['L2_violations'].append((w, c, bad, f'size {len(bad)} != d={d}'))
                    continue
                # Check coset structure: bad - bad[0] should equal subgroup
                bad_list = sorted(bad)
                k0 = bad_list[0]
                shifted = {(k - k0) % n for k in bad}
                if shifted != subgroup:
                    results['L2_ok'] = False
                    results['L2_violations'].append((w, c, bad, f'not coset of <{n1}>'))

    return results


def main():
    with open(CSV) as f:
        rows = [r for r in csv.DictReader(f) if r['stratum'] == 'L_residual']

    print(f"L_residual cases: {len(rows)}\n")
    print(f"{'n':>2} {'G':<14} {'A':<10} {'p':>2}  L1   L2   L3")

    sr_failure_cases = 0
    L1_total_ok = 0
    L2_total_ok = 0
    L3_total_ok = 0
    summary = {'L1_violations': [], 'L2_violations': [], 'L3_violations': []}

    for r in rows:
        n = int(r['n'])
        G = parse_speeds(r['G_speeds'])
        A = parse_speeds(r['A_speeds'])
        p = int(r['p'])
        W = list(G) + [p * u for u in A]
        W2 = [w // n for w in W if w % n == 0]
        if not W2:
            continue  # SR-success, skip
        W1 = [w for w in W if w % n != 0]
        sr_failure_cases += 1

        res = check_L1_L2_L3(n, W1)
        L1 = 'OK' if res['L1_ok'] else 'FAIL'
        L2 = 'OK' if res['L2_ok'] else 'FAIL'
        L3 = 'OK' if res['L3_ok'] else 'FAIL'

        L1_total_ok += res['L1_ok']
        L2_total_ok += res['L2_ok']
        L3_total_ok += res['L3_ok']

        for vk in ['L1_violations', 'L2_violations', 'L3_violations']:
            summary[vk].extend(res[vk])

        print(f"{n:>2} {str(G):<14} {str(A):<10} {p:>2}  {L1:<5} {L2:<5} {L3:<5}")

    print(f"\nSR-failure cases checked: {sr_failure_cases}")
    print(f"L1 (coprime bad-k = {{0, -w^-1}}, c-independent): {L1_total_ok}/{sr_failure_cases}")
    print(f"L2 (non-coprime bad-k = coset of <n/d>, size d): {L2_total_ok}/{sr_failure_cases}")
    print(f"L3 (coprime bad-k disjoint from non-units):       {L3_total_ok}/{sr_failure_cases}")

    if summary['L1_violations']:
        print(f"\nL1 violations: {summary['L1_violations'][:5]}")
    if summary['L2_violations']:
        print(f"\nL2 violations: {summary['L2_violations'][:5]}")
    if summary['L3_violations']:
        print(f"\nL3 violations: {summary['L3_violations'][:5]}")

    # Now also check the safe non-unit principle by stratum
    print("\n" + "=" * 60)
    print("Safe non-unit principle for composite n:")
    print("Cases where some unit c gives a non-unit safe k:")
    print("=" * 60)
    for r in rows:
        n = int(r['n'])
        G = parse_speeds(r['G_speeds'])
        A = parse_speeds(r['A_speeds'])
        p = int(r['p'])
        W = list(G) + [p * u for u in A]
        W2 = [w // n for w in W if w % n == 0]
        if not W2:
            continue
        W1 = [w for w in W if w % n != 0]
        units_c = [c for c in range(1, n) if math.gcd(c, n) == 1]
        S_n = {k for k in range(1, n) if 1 < math.gcd(k, n) < n}

        for c in units_c:
            bad_all = set()
            for w in W1:
                bad_all |= bad_k_set(n, w, c)
            safe_nonunit = (set(range(n)) - bad_all) & S_n
            safe_any = set(range(n)) - bad_all
            if safe_nonunit:
                tag = f"unit c={c}: safe non-unit k={sorted(safe_nonunit)}"
                break
        else:
            tag = "NO unit c gives safe non-unit k"
            safe_any_at_any_c = False
            for c in units_c:
                bad_all = set()
                for w in W1:
                    bad_all |= bad_k_set(n, w, c)
                if set(range(n)) - bad_all:
                    safe_any_at_any_c = True
                    break
            tag += f"; safe-any-k at some unit c? {safe_any_at_any_c}"

        primes = (n in {2, 3, 5, 7, 11, 13})
        print(f"  n={n:>2} prime={primes}  G={str(G):<13} A={str(A):<9} p={p:>2}  {tag}")


if __name__ == "__main__":
    main()
