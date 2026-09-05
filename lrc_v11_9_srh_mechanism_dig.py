"""
DIG into why the 45 'residual' cases have witnesses.

For each residual case:
  1. Find ALL (k, c) joint witnesses on lattice 1/n^2.
  2. For each witness, decompose: list which runners contribute which bad-k
     elements at this (k, c).
  3. Identify OVERLAPS: pairs of runners whose bad-sets share elements.
  4. Classify the overlap MECHANISMS:
     - small-overlap: pairs of small (w<n) coprime runners share 0 at β=0.
     - residue-class-overlap: same residue mod n, consecutive β's.
     - cross-residue: w_b ≡ β_b · w_a mod n algebraic identity.
     - non-coprime-boundary: w with gcd>1 vanishes (empty bad-k).
     - non-coprime-cover: w with gcd>1 contributes a coset overlapping with pair.
     - other: unclassified.

The point: find the UNIFYING mechanism rather than enumerate sub-cases.
"""
import csv
import math
from collections import defaultdict, Counter

CSV6 = "/Users/trentpalelei/Desktop/Math Ex/reports/phase6_residual_arithmetic.csv"
CSV7 = "/Users/trentpalelei/Desktop/Math Ex/reports/phase7a_extended_search.csv"


def parse_speeds(s):
    return [int(x) for x in s.split("-")]


def norm_int(num, den):
    return min(num % den, den - num % den)


def w1_decomp(n, G, A, p):
    W = list(G) + [p * u for u in A]
    W1 = [w for w in W if w % n != 0]
    W2 = [w // n for w in W if w % n == 0]
    return W, W1, W2


def bad_k_for(n, w, c):
    n2 = n * n
    return {k for k in range(n) if norm_int(w * (n * k + c), n2) * n < n2}


def z2_good(n, W2):
    return [c for c in range(1, n) if all((w * c) % n != 0 for w in W2)]


def classify_overlap(n, W1, c, k_good):
    """For the witness (k_good, c), classify which pairs of runners overlap at
    which elements, and what mechanism creates each overlap."""
    bad_per_w = {w: bad_k_for(n, w, c) for w in W1}
    overlaps = []  # (w_a, w_b, shared_k, mechanism)
    for i, w_a in enumerate(W1):
        d_a = math.gcd(w_a, n)
        for j in range(i + 1, len(W1)):
            w_b = W1[j]
            d_b = math.gcd(w_b, n)
            shared = bad_per_w[w_a] & bad_per_w[w_b]
            for k in shared:
                if d_a == 1 and d_b == 1:
                    # both coprime — pair overlap
                    # Classify mechanism
                    if w_a < n and w_b < n and k == 0:
                        mech = 'small_overlap'
                    elif w_a % n == w_b % n:
                        mech = 'same_residue_chain'
                    else:
                        # check cross-residue: w_b ≡ β_b · w_a mod n
                        beta_a = (w_a * c // n) % n
                        beta_b = (w_b * c // n) % n
                        if (beta_b * w_a) % n == w_b % n:
                            mech = 'cross_residue_alpha'
                        elif (beta_a * w_b) % n == w_a % n:
                            mech = 'cross_residue_beta'
                        else:
                            mech = 'coprime_other'
                else:
                    mech = 'non_coprime_overlap'
                overlaps.append((w_a, w_b, k, mech))
    return bad_per_w, overlaps


def analyze_case(case_idx, n, G, A, p):
    W, W1, W2 = w1_decomp(n, G, A, p)
    z2g = z2_good(n, W2)
    n2 = n * n

    # Find all witnesses
    witnesses = []
    for c in z2g:
        bad_union = set()
        for w in W1:
            bad_union |= bad_k_for(n, w, c)
        good_k = set(range(n)) - bad_union
        if good_k:
            witnesses.append((c, sorted(good_k), len(bad_union)))

    return W, W1, W2, z2g, witnesses


def main():
    cases = []
    with open(CSV6) as f:
        for r in csv.DictReader(f):
            if r['stratum'] != 'L_residual':
                continue
            cases.append({'n': int(r['n']), 'G': parse_speeds(r['G_speeds']),
                         'A': parse_speeds(r['A_speeds']), 'p': int(r['p'])})
    with open(CSV7) as f:
        for r in csv.DictReader(f):
            n = int(r['n']); kG = int(r['kG']); kA = int(r['kA'])
            if kG + kA != n - 1:
                continue
            if r['pigeonhole_holds'] not in ('0', 'False', 'false'):
                continue
            if int(r['N_joint']) <= 0:
                continue
            cases.append({'n': n, 'G': parse_speeds(r['G_speeds']),
                         'A': parse_speeds(r['A_speeds']), 'p': int(r['p'])})

    # Filter to residual: SR fails, and existing sub-lemmas don't apply
    residual = []
    for c in cases:
        n, G, A, p = c['n'], c['G'], c['A'], c['p']
        W, W1, W2 = w1_decomp(n, G, A, p)
        if not W2:
            continue  # SR closes
        all_coprime = all(math.gcd(w, n) == 1 for w in W1)
        if all_coprime and all(w < n for w in W1):
            continue  # SR-H/small
        # Check chain-overlap (all q's start from 0 in consecutive intervals)
        if all_coprime:
            residues_q = defaultdict(list)
            for w in W1:
                residues_q[w % n].append(w // n)
            chain = all(sorted(qs) == list(range(len(qs))) for qs in residues_q.values()) \
                and all(0 in qs for qs in residues_q.values())
            if chain:
                continue
        if len(W1) == 2 and all_coprime and (W1[0] + W1[1]) % (2 * n) == 0:
            continue
        residual.append(c)

    print(f"Residual cases (not covered by SR + sub-lemmas): {len(residual)}\n")

    mechanism_counts = Counter()
    # Detailed analysis of a few
    for case_idx, c in enumerate(residual[:6]):
        n, G, A, p = c['n'], c['G'], c['A'], c['p']
        W, W1, W2, z2g, witnesses = analyze_case(case_idx, n, G, A, p)
        print(f"=== Case {case_idx}: n={n}, G={G}, A={A}, p={p} ===")
        print(f"  W={W}, W1={W1}, W2={W2}")
        print(f"  Z2-good c: {z2g}")
        print(f"  Witnesses (c, good_k_set, |bad_union|):")
        for c_val, good_k, badct in witnesses[:3]:
            print(f"    c={c_val}: good_k={good_k}, bad_union_size={badct}")
        # Pick first witness, analyze overlaps
        if witnesses:
            c_use = witnesses[0][0]
            k_good = witnesses[0][1][0]
            bad_per_w, overlaps = classify_overlap(n, W1, c_use, k_good)
            print(f"  Bad sets at c={c_use}:")
            for w in W1:
                print(f"    w={w} (gcd={math.gcd(w,n)}): bad-k={sorted(bad_per_w[w])}")
            print(f"  Pairwise overlaps at c={c_use}:")
            for w_a, w_b, kk, mech in overlaps:
                print(f"    {w_a}, {w_b} share k={kk}: {mech}")
                mechanism_counts[mech] += 1
        print()

    print("=== Overlap mechanism counts (first 6 cases) ===")
    for mech, cnt in mechanism_counts.most_common():
        print(f"  {mech}: {cnt}")

    # Now: across ALL residual cases, count mechanism distribution at first witness
    print("\n=== Mechanism distribution across ALL residual cases (first witness) ===")
    total_mechanisms = Counter()
    for case in residual:
        n, G, A, p = case['n'], case['G'], case['A'], case['p']
        W, W1, W2, z2g, witnesses = analyze_case(0, n, G, A, p)
        if witnesses:
            c_use = witnesses[0][0]
            k_good = witnesses[0][1][0]
            _, overlaps = classify_overlap(n, W1, c_use, k_good)
            mechs = {o[3] for o in overlaps}
            for m in mechs:
                total_mechanisms[m] += 1
    for mech, cnt in total_mechanisms.most_common():
        print(f"  {mech}: appears in {cnt}/{len(residual)} cases")


if __name__ == "__main__":
    main()
