#!/usr/bin/env python3
"""
Verify the analytical claim for Theorem 12.1 Case B.

KEY CLAIM: For n=pq (squarefree semiprime, p<q), dropped non-units d1,d2,
all divisible runners having n|q_j, and any |E_div|>=2:

At fibre b = L/q + delta (where delta is chosen to make all divisible runners
transparent and delta < L/(n-1) so non-divisible floor states are unchanged):

  1. All retained gcd=q runners are transparent (Silence Lemma):
     T_rho = floor(rho*L/q / L) = floor(rho/q) = floor(jq/q) = j  for rho = jq
     Since j in {1,...,p-1}: T%q = j != 0 and (T+1)%q = j+1 <= p < q != 0.

  2. Unit runner coverage of H_q\{0}:
     - Unit rho with T_rho < p-1: can NOT cover any element of H_q\{0}
       (proved: -T_rho * rho^{-1} mod n is not a multiple of p, the generator of H_q)
     - Unit rho with T_rho = p-1 (rho in [(p-1)q, pq)): covers exactly ONE element
       kp = -p*rho^{-1} mod n

  3. Number of T=p-1 unit runners = q - 1 - floor(q/p)
     (= q - 1 - number of multiples of p in [(p-1)q, pq))
     
  4. Miss set intersection H_q\{0} has exactly floor(q/p) >= 1 elements.
     => Miss set is non-empty! Safe fibre exists.
"""

from math import gcd, floor

def units_mod_n(n):
    return [r for r in range(1, n) if gcd(r, n) == 1]

def h_q_group(p, q):
    """H_q = multiples of p in Z/(pq)Z = {0, p, 2p,...,(q-1)p}"""
    n = p * q
    return {k * p % n for k in range(q)}

def bad_set(rho, T, n):
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

def verify_silence_lemma_fibre(n, p, q, d1, d2):
    """
    Verify the analytical claims at b = L/q (Silence Lemma fibre).
    Returns miss set and decomposes coverage.
    """
    assert n == p * q
    assert gcd(p, q) == 1

    retained = [r for r in range(1, n) if r not in (d1, d2)]
    units = [r for r in retained if gcd(r, n) == 1]
    gcd_p_runners = [r for r in retained if gcd(r, n) == p]
    gcd_q_runners = [r for r in retained if gcd(r, n) == q]

    Hq = h_q_group(p, q)
    Hq_nonzero = Hq - {0}

    # At b = L/q: T_rho = floor(rho / q) for each non-divisible runner
    coverage = set()
    unit_coverage_Hq = set()

    # Check each runner type
    gcd_q_silent = True
    for rho in gcd_q_runners:
        j = rho // q
        T = j  # floor(jq/q) = j
        Tmod_q = T % q
        Tp1mod_q = (T + 1) % q
        if Tmod_q == 0 or Tp1mod_q == 0:
            gcd_q_silent = False
        bs = bad_set(rho, T, n)
        coverage |= bs

    for rho in gcd_p_runners:
        T = rho // q
        bs = bad_set(rho, T, n)
        coverage |= bs

    # Unit runners: classify by T value
    T_eq_pm1_units = []
    T_lt_pm1_units = []
    for rho in units:
        T = rho // q
        if T == p - 1:
            T_eq_pm1_units.append(rho)
        else:
            T_lt_pm1_units.append(rho)

    # Verify: T<p-1 units can't cover H_q\{0}
    for rho in T_lt_pm1_units:
        T = rho // q
        bs = bad_set(rho, T, n)
        hq_hit = bs & Hq_nonzero
        if hq_hit:
            print(f"  ERROR: T<p-1 unit rho={rho} covers H_q element(s) {hq_hit}")
        coverage |= bs

    # T=p-1 units: each should cover exactly 1 element of H_q\{0}
    elements_covered_by_T_pm1 = set()
    for rho in T_eq_pm1_units:
        T = p - 1
        bs = bad_set(rho, T, n)
        hq_hit = bs & Hq_nonzero
        elements_covered_by_T_pm1 |= hq_hit
        coverage |= bs

    miss = set(range(n)) - coverage

    # Count multiples of p in [(p-1)q, pq)
    count_div_p = sum(1 for r in range((p-1)*q, p*q) if r % p == 0)

    print(f"\nn={n}={p}*{q}, dropped=({d1},{d2})")
    print(f"  Silence Lemma: gcd=q runners silent at b=L/q: {gcd_q_silent}")
    print(f"  |T=p-1 units|={len(T_eq_pm1_units)}, expected q-1-floor(q/p)={q-1-q//p}")
    print(f"  |H_q\\{{0}}|={len(Hq_nonzero)}, elements covered by T=p-1 units={len(elements_covered_by_T_pm1)}")
    print(f"  floor(q/p)={q//p}, expected miss in H_q\\{{0}}={q//p}")
    print(f"  Actual miss: {sorted(miss)}")
    print(f"  Miss ∩ H_q\\{{0}}: {sorted(miss & Hq_nonzero)}")
    print(f"  |Miss ∩ H_q\\{{0}}| = {len(miss & Hq_nonzero)}, floor(q/p)={q//p}")
    assert len(miss & Hq_nonzero) == q // p, f"Mismatch! got {len(miss & Hq_nonzero)}, expected {q//p}"
    assert len(miss) > 0, "Miss set is empty!"
    print(f"  ✓ Miss set non-empty with floor(q/p)={q//p} elements in H_q\\{{0}}")
    return miss

def verify_case_c_perturbation(n, p, q, d1, d2, div_qs, miss_at_Lq):
    """
    Verify that perturbed fibre b = L/q + delta works for Case C.
    delta is chosen to make ALL divisible runners transparent
    while keeping non-divisible floor states unchanged.
    """
    from math import lcm
    from functools import reduce

    retained = [r for r in range(1, n) if r not in (d1, d2)]

    # Build L = lcm of all speeds
    speeds = retained + [q_j * n for q_j in div_qs]
    L = reduce(lcm, speeds)

    b_Lq = L // q  # fibre L/q (integer)

    # Find delta: search in [1, L//n] for one making all divisible runners transparent
    delta_found = None
    for delta in range(1, L // n + 1):
        b = b_Lq + delta
        if b > (n - 1) * L // n:
            break
        div_ok = True
        for q_j in div_qs:
            T = (q_j * n * b) // L
            if T % n == 0 or T % n == n - 1:
                div_ok = False
                break
        if div_ok:
            delta_found = delta
            break

    if delta_found is None:
        print(f"  ERROR: No valid delta found!")
        return

    b_dag = b_Lq + delta_found
    print(f"\n  Case C perturbation: delta={delta_found}, b†={b_dag}")
    print(f"  b†/L = {b_dag}/{L} ≈ {b_dag/L:.6f}")
    print(f"  In B_div: [{L//n}, {(n-1)*L//n}]? {L//n <= b_dag <= (n-1)*L//n}")

    # Verify non-divisible floor states unchanged
    for rho in retained:
        T_at_Lq = rho * (L // q) // L
        T_at_dag = rho * b_dag // L
        if T_at_Lq != T_at_dag:
            print(f"  WARNING: floor state changed for rho={rho}: {T_at_Lq} -> {T_at_dag}")

    # Compute coverage at b†
    coverage = set()
    for rho in retained:
        T = rho * b_dag // L
        bs = bad_set(rho, T, n)
        coverage |= bs
    for q_j in div_qs:
        T = q_j * n * b_dag // L
        bs = bad_set(q_j * n, T, n)
        if len(bs) == n:
            print(f"  ERROR: Divisible runner q_j={q_j} blocks fibre b†!")
        coverage |= bs

    miss_dag = set(range(n)) - coverage
    print(f"  Miss at b†: {sorted(miss_dag)}")
    print(f"  Same as miss at L/q: {miss_dag == miss_at_Lq}")
    assert len(miss_dag) > 0, "Miss set empty at b†!"
    print(f"  ✓ Safe fibre b† found with |miss|={len(miss_dag)}")

print("=" * 70)
print("ANALYTICAL VERIFICATION: THEOREM 12.1 CASE B — SILENCE LEMMA APPROACH")
print("=" * 70)

# Test cases: squarefree semiprimes n=pq
test_cases = [
    (15, 3, 5, 3, 6),    # n=15, drop (3,6): both gcd=3
    (15, 3, 5, 5, 10),   # n=15, drop (5,10): both gcd=5
    (15, 3, 5, 3, 5),    # n=15, drop (3,5): mixed
    (21, 3, 7, 3, 6),    # n=21, drop (3,6)
    (21, 3, 7, 7, 14),   # n=21, drop (7,14): both gcd=7
    (35, 5, 7, 5, 10),   # n=35, drop (5,10)
    (35, 5, 7, 7, 14),   # n=35, drop (7,14)
    (33, 3, 11, 3, 6),   # n=33, drop (3,6)
    (55, 5, 11, 5, 10),  # n=55, drop (5,10)
]

print("\n─── PART 1: Silence Lemma miss set at b=L/q ───")
for (n, p, q, d1, d2) in test_cases:
    miss = verify_silence_lemma_fibre(n, p, q, d1, d2)

print("\n─── PART 2: Case C perturbation (all n|q_j) ───")
case_c_tests = [
    (15, 3, 5, 3, 6, [15, 30]),    # q_j=15,30: both divisible by n=15
    (15, 3, 5, 5, 10, [15, 30]),   # same divisors, different drop
    (21, 3, 7, 3, 6, [21, 42]),    # n=21
    (21, 3, 7, 3, 6, [21, 63]),    # n=21, second is 3n
    (33, 3, 11, 3, 6, [33, 66]),   # n=33
]

for (n, p, q, d1, d2, div_qs) in case_c_tests:
    miss_Lq = verify_silence_lemma_fibre(n, p, q, d1, d2)
    verify_case_c_perturbation(n, p, q, d1, d2, div_qs, miss_Lq)

