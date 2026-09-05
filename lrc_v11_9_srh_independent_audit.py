"""
Independent audit of the SR-H findings.

Verifies, with NO reliance on the previous structure-check script:

  (A) For each of the 4 claimed counterexample cases, EVERY unit c
      yields ALL k in {0,...,n-1} as bad.
  (B) For each of those 4 cases, SOME non-unit Z2-good c yields a witness.
  (C) For each of the OTHER 30 SR-failure cases, SOME unit c yields a witness.
  (D) L1 (corrected) formula: for gcd(w,n)=1, bad-k = {-β·w⁻¹, -(β+1)·w⁻¹} mod n
      where β = ⌊wc/n⌋ mod n, and this holds for ALL c in {1,...,n-1}
      (not just units). Verified case by case.
  (E) L2 formula: for gcd(w,n)=d>1, bad-k is either empty or a coset of <n/d>
      of size d.
  (F) Numerical sanity: the empirical 34/34 empirical script's reported witnesses
      are indeed witnesses (re-check directly).
"""

import csv
import math

CSV = "/Users/trentpalelei/Desktop/Math Ex/reports/phase6_residual_arithmetic.csv"


def parse_speeds(s):
    return [int(x) for x in s.split("-")]


def norm_int(num, den):
    r = num % den
    return min(r, den - r)


def bad_k_set_direct(n, w, c):
    """Direct: compute bad_k(w,c) by iterating over k in {0,...,n-1}."""
    n2 = n * n
    return {k for k in range(n) if norm_int(w * (n * k + c), n2) * n < n2}


def bad_k_set_L1(n, w, c):
    """Predicted by L1 (corrected) for gcd(w,n)=1."""
    if math.gcd(w, n) != 1:
        raise ValueError("L1 only applies for gcd(w,n)=1")
    w_inv = pow(w, -1, n)
    beta = (w * c) // n % n
    k1 = (-beta * w_inv) % n
    k2 = (-(beta + 1) * w_inv) % n
    return {k1, k2}


def bad_k_set_L2(n, w, c):
    """Predicted by L2 for gcd(w,n)=d>1, CORRECTED.

    The orbit X(k) lives in the coset wc + nd·Z/n². As k varies 0..n-1, X(k) cycles
    through n_1 = n/d distinct values, each visited d times. Bad orbit values are those
    in {0..n-1} ∪ {n²-n+1..n²-1}. Find which k's hit them.

    Implementation: orbit-index labeling α (X(k)=wc+k·wn mod n²) is the natural one;
    converting from "γ + j'·nd" labeling β requires adjusting by s = ⌊wc/nd⌋.
    """
    d = math.gcd(w, n)
    if d == 1 or d == n:
        raise ValueError("L2 only applies for 1 < gcd(w,n) < n")
    n1 = n // d
    w1 = w // d
    rp = (w1 * c) % n
    R_d = set(range(0, n1)) | set(range(n - n1 + 1, n))
    if rp not in R_d:
        return set()
    gamma = d * rp
    nd = n * d
    # j'_β (the index in {γ + j'·nd : j' ∈ {0,..,n_1-1}}) is 0 if γ ≤ n-1, n_1-1 if γ ≥ nd-n+1.
    if 0 <= gamma <= n - 1:
        jp_beta = 0
    elif nd - n + 1 <= gamma <= nd - 1:
        jp_beta = n1 - 1
    else:
        return set()
    # Convert to α-labeling: s := ⌊wc/nd⌋ mod n_1, then j'_α = (j'_β - s)·w_1⁻¹ mod n_1.
    # Note: γ = wc mod nd, so wc = γ + (⌊wc/nd⌋)·nd.
    s = ((w * c) // nd) % n1
    w1_inv_mod_n1 = pow(w1 % n1, -1, n1)
    jp_alpha = ((jp_beta - s) * w1_inv_mod_n1) % n1
    # k satisfies k ≡ jp_alpha mod n_1
    return {(jp_alpha + i * n1) % n for i in range(d)}


def bad_k_coset_property(n, w, c):
    """Looser L2 check: bad-k is either empty OR a coset of <n/d> of size d."""
    d = math.gcd(w, n)
    if d == 1 or d == n:
        raise ValueError("Only for 1 < gcd(w,n) < n")
    n1 = n // d
    bad = bad_k_set_direct(n, w, c)
    if len(bad) == 0:
        return True
    if len(bad) != d:
        return False
    subgroup = {(i * n1) % n for i in range(d)}
    bad_list = sorted(bad)
    k0 = bad_list[0]
    shifted = {(k - k0) % n for k in bad}
    return shifted == subgroup


def is_witness(n, G, A, p, c, k):
    """Check if t = (n*k + c)/n^2 is a joint witness."""
    n2 = n * n
    m = n * k + c
    for v in G:
        if norm_int(v * m, n2) * n < n2:
            return False
    pt_num = (p * m) % n2
    for u in A:
        if norm_int(u * pt_num, n2) * n < n2:
            return False
    return True


def z2_good(n, W2):
    return [c for c in range(1, n) if all((w * c) % n != 0 for w in W2)]


def main():
    with open(CSV) as f:
        rows = [r for r in csv.DictReader(f) if r['stratum'] == 'L_residual']

    sr_failure_rows = []
    for r in rows:
        n = int(r['n'])
        G = parse_speeds(r['G_speeds'])
        A = parse_speeds(r['A_speeds'])
        p = int(r['p'])
        W = list(G) + [p * u for u in A]
        W2 = [w // n for w in W if w % n == 0]
        if W2:
            sr_failure_rows.append((n, G, A, p, W, W2))

    print(f"Total SR-failure cases: {len(sr_failure_rows)}\n")

    # Audits (A), (B), (C): unit-c verification
    cases_no_unit_witness = []
    cases_unit_witness = []
    for (n, G, A, p, W, W2) in sr_failure_rows:
        units = [c for c in range(1, n) if math.gcd(c, n) == 1]
        any_unit_witness = False
        for c in units:
            for k in range(n):
                if is_witness(n, G, A, p, c, k):
                    any_unit_witness = True
                    break
            if any_unit_witness:
                break
        if any_unit_witness:
            cases_unit_witness.append((n, G, A, p))
        else:
            cases_no_unit_witness.append((n, G, A, p, W, W2))

    print("=" * 70)
    print("AUDIT (A,B,C): unit-c witness check")
    print("=" * 70)
    print(f"Cases with unit-c witness:     {len(cases_unit_witness)}/{len(sr_failure_rows)}")
    print(f"Cases without unit-c witness:  {len(cases_no_unit_witness)}/{len(sr_failure_rows)}\n")
    print("Cases WITHOUT unit-c witness (claimed counterexamples):")
    for (n, G, A, p, W, W2) in cases_no_unit_witness:
        # check non-unit Z2-good witness exists
        z2g = z2_good(n, W2)
        non_unit_z2g = [c for c in z2g if math.gcd(c, n) != 1]
        any_non_unit_witness = False
        witness_cks = []
        for c in non_unit_z2g:
            for k in range(n):
                if is_witness(n, G, A, p, c, k):
                    witness_cks.append((c, k))
                    any_non_unit_witness = True
        print(f"  n={n}, G={G}, A={A}, p={p}, W2={W2}, Z2-good non-units={non_unit_z2g}")
        print(f"    non-unit witness exists: {any_non_unit_witness}")
        print(f"    witnesses (c,k): {witness_cks[:5]}{' ...' if len(witness_cks) > 5 else ''}")

    # Audit (D): L1 formula
    print("\n" + "=" * 70)
    print("AUDIT (D): L1 (corrected) formula — for gcd(w,n)=1 and all c in {1,...,n-1}")
    print("=" * 70)
    l1_violations = []
    for (n, G, A, p, W, W2) in sr_failure_rows:
        W1 = [w for w in W if w % n != 0]
        for w in W1:
            if math.gcd(w, n) != 1:
                continue
            for c in range(1, n):
                bad_direct = bad_k_set_direct(n, w, c)
                bad_L1 = bad_k_set_L1(n, w, c)
                if bad_direct != bad_L1:
                    l1_violations.append((n, w, c, bad_direct, bad_L1))
    if l1_violations:
        print(f"L1 violations: {len(l1_violations)} (first 5 shown):")
        for v in l1_violations[:5]:
            print(f"  {v}")
    else:
        print("L1: NO violations across ALL (n, w coprime, c) tuples in 34 cases. ✓")

    # Audit (E.1): L2 structural property — coset of <n/d> of size d, or empty
    print("\n" + "=" * 70)
    print("AUDIT (E.1): L2 structural property — bad-k is empty or coset of <n/d>, size d")
    print("=" * 70)
    e1_violations = []
    for (n, G, A, p, W, W2) in sr_failure_rows:
        W1 = [w for w in W if w % n != 0]
        for w in W1:
            d = math.gcd(w, n)
            if d == 1 or d == n:
                continue
            for c in range(1, n):
                if not bad_k_coset_property(n, w, c):
                    e1_violations.append((n, w, c))
    if e1_violations:
        print(f"E.1 violations: {len(e1_violations)} (first 5):")
        for v in e1_violations[:5]:
            print(f"  {v}")
    else:
        print("E.1: NO violations across ALL (n, w non-coprime, c) tuples in 34 cases. ✓")

    # Audit (E.2): L2 specific formula (corrected)
    print("\n" + "=" * 70)
    print("AUDIT (E.2): L2 specific-coset formula (corrected with s = ⌊wc/nd⌋)")
    print("=" * 70)
    e2_violations = []
    for (n, G, A, p, W, W2) in sr_failure_rows:
        W1 = [w for w in W if w % n != 0]
        for w in W1:
            d = math.gcd(w, n)
            if d == 1 or d == n:
                continue
            for c in range(1, n):
                bad_direct = bad_k_set_direct(n, w, c)
                bad_L2 = bad_k_set_L2(n, w, c)
                if bad_direct != bad_L2:
                    e2_violations.append((n, w, c, bad_direct, bad_L2))
    if e2_violations:
        print(f"E.2 violations: {len(e2_violations)} (first 5):")
        for v in e2_violations[:5]:
            print(f"  {v}")
    else:
        print("E.2: NO violations across ALL (n, w non-coprime, c) tuples in 34 cases. ✓")

    # Audit (F): empirical 34/34 sanity
    print("\n" + "=" * 70)
    print("AUDIT (F): empirical witness check (any Z2-good c)")
    print("=" * 70)
    all_have_witness = 0
    for (n, G, A, p, W, W2) in sr_failure_rows:
        z2g = z2_good(n, W2)
        found = False
        for c in z2g:
            for k in range(n):
                if is_witness(n, G, A, p, c, k):
                    found = True
                    break
            if found:
                break
        if found:
            all_have_witness += 1
        else:
            print(f"  WITNESS NOT FOUND for n={n}, G={G}, A={A}, p={p}")
    print(f"Cases with ANY Z2-good c witness: {all_have_witness}/{len(sr_failure_rows)}")


if __name__ == "__main__":
    main()
