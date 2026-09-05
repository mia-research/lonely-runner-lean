"""
Angle (a): characterize structural invariant separating the 4 unit-c counterexamples
from the 30 working cases.

For each SR-failure case, compute candidate invariants and tabulate.
Look for invariants that take a specific value/range on counterexamples
and a different value/range on working cases.

Candidate invariants:
  I1  |W_1|
  I2  |W_1^{cop}|  (coprime to n)
  I3  |W_1^{>1}|  (non-coprime to n)
  I4  symmetric_pairs_2n: number of {w_a, w_b} ⊂ W_1 with w_a + w_b ≡ 0 mod 2n
  I5  pair_count(W_1, n): #{(w_a, w_b) ⊂ W_1 : w_a ≡ -w_b mod n}  (mod-n complements)
  I6  distinct_residues: |{w mod n : w ∈ W_1}|
  I7  sum_gcd: Σ_{w∈W_1} gcd(w, n)
  I8  min_unit_K: min over unit Z2-good c of |K(c)|  (≤ n always; = n is counterexample)
  I9  has_pair_residues_summing_to_0: bool indicating Σ residues mod n
  I10 d_distribution: distribution of gcd(w, n) for w ∈ W_1
  I11 w_1 mod n_1 distribution
"""
import csv
import math
from collections import Counter

CSV = "/Users/trentpalelei/Desktop/Math Ex/reports/phase6_residual_arithmetic.csv"


def parse_speeds(s):
    return [int(x) for x in s.split("-")]


def norm_int(num, den):
    r = num % den
    return min(r, den - r)


def bad_k_set(n, w, c):
    n2 = n * n
    return {k for k in range(n) if norm_int(w * (n * k + c), n2) * n < n2}


def z2_good(n, W2):
    return [c for c in range(1, n) if all((w * c) % n != 0 for w in W2)]


def compute_invariants(n, G, A, p):
    W = list(G) + [p * u for u in A]
    W2 = [w // n for w in W if w % n == 0]
    W1 = [w for w in W if w % n != 0]

    I1 = len(W1)
    I2 = sum(1 for w in W1 if math.gcd(w, n) == 1)
    I3 = I1 - I2

    # I4: symmetric pairs at 2n
    I4 = sum(1 for i in range(len(W1)) for j in range(i+1, len(W1))
             if (W1[i] + W1[j]) % (2 * n) == 0)

    # I5: mod-n complement pairs
    I5 = sum(1 for i in range(len(W1)) for j in range(i+1, len(W1))
             if (W1[i] + W1[j]) % n == 0)

    # I6: distinct residues mod n
    I6 = len({w % n for w in W1})

    # I7: sum of gcds
    I7 = sum(math.gcd(w, n) for w in W1)

    # I8: min over unit Z2-good c of |K(c)|
    z2g_units = [c for c in z2_good(n, W2) if math.gcd(c, n) == 1]
    if z2g_units:
        min_K = min(sum(1 for _ in (k for k in range(n)
                                    if any(k in bad_k_set(n, w, c) for w in W1)))
                    for c in z2g_units)
    else:
        min_K = -1

    # I9: distribution of gcd
    d_dist = tuple(sorted(Counter(math.gcd(w, n) for w in W1).items()))

    # I10: count Z2-good c (units and non-units)
    z2g_all = z2_good(n, W2)
    I10 = (len(z2g_all), sum(1 for c in z2g_all if math.gcd(c, n) == 1))

    # I11: |W_1| + |W_2|
    I11 = I1 + len(W2)

    return {
        'n': n, 'G': G, 'A': A, 'p': p,
        'W1': W1, 'W2': W2,
        'I1_W1': I1, 'I2_cop': I2, 'I3_noncop': I3,
        'I4_sym_2n': I4, 'I5_complement_n': I5,
        'I6_distinct_res': I6, 'I7_sum_gcd': I7,
        'I8_min_unit_K': min_K,
        'I9_d_dist': d_dist,
        'I10_z2g_total_unit': I10,
        'I11_W1_W2': I11,
    }


def main():
    with open(CSV) as f:
        rows = [r for r in csv.DictReader(f) if r['stratum'] == 'L_residual']

    cases = []
    for r in rows:
        n = int(r['n'])
        G = parse_speeds(r['G_speeds'])
        A = parse_speeds(r['A_speeds'])
        p = int(r['p'])
        W = list(G) + [p * u for u in A]
        W2 = [w // n for w in W if w % n == 0]
        if W2:
            inv = compute_invariants(n, G, A, p)
            cases.append(inv)

    # Identify counterexamples: I8_min_unit_K == n
    counterexample_cases = [c for c in cases if c['I8_min_unit_K'] == c['n']]
    working_cases = [c for c in cases if c['I8_min_unit_K'] != c['n']]

    print(f"Total SR-failure: {len(cases)}")
    print(f"Counterexamples (no unit c witness): {len(counterexample_cases)}")
    print(f"Working (some unit c gives witness): {len(working_cases)}\n")

    print("=" * 110)
    print("Counterexamples:")
    print("=" * 110)
    keys = ['n', 'I1_W1', 'I2_cop', 'I3_noncop', 'I4_sym_2n', 'I5_complement_n',
            'I6_distinct_res', 'I7_sum_gcd', 'I9_d_dist']
    header = f"  {'idx':<3} " + " ".join(f"{k:<14}" for k in keys) + "  W1"
    print(header)
    for i, c in enumerate(counterexample_cases):
        vals = " ".join(f"{str(c[k]):<14}" for k in keys)
        print(f"  {i:<3} {vals}  {c['W1']}")

    print("\n" + "=" * 110)
    print("Working cases (first 15):")
    print("=" * 110)
    print(header)
    for i, c in enumerate(working_cases[:15]):
        vals = " ".join(f"{str(c[k]):<14}" for k in keys)
        print(f"  {i:<3} {vals}  {c['W1']}")

    # Check each candidate invariant for separation
    print("\n" + "=" * 110)
    print("Invariant separation check:")
    print("=" * 110)
    for k in keys[1:]:  # skip 'n'
        ce_vals = set(str(c[k]) for c in counterexample_cases)
        wo_vals = set(str(c[k]) for c in working_cases)
        overlap = ce_vals & wo_vals
        if not overlap:
            print(f"  {k:<20} SEPARATES (CE: {ce_vals}, WO {len(wo_vals)} values)")
        else:
            print(f"  {k:<20} overlaps: CE {ce_vals} ∩ WO = {overlap}")


if __name__ == "__main__":
    main()
