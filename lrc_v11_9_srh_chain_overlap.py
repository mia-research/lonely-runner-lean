"""
Theorem SR-H/chain-overlap (candidate sub-lemma):

If W_1 is all coprime to n, and for every residue r in R(W_1) := {w mod n : w in W_1}
  - some element w_r in W_1 has w_r ≡ r mod n with w_r < n (i.e., 0 in Q_r), AND
  - Q_r is a consecutive interval [0, m_r - 1],

then at c = 1:
  |bad-k union| = sum_r |Q_r ∪ (Q_r+1)| - (overlap_count_at_0)
                = sum_r (m_r + 1) - (|R| - 1)
                = |W_1| + |R| - |R| + 1
                = |W_1| + 1
                ≤ n - 1.

So c=1 works. Equivalently: if W_1 splits cleanly into "residue chains" starting at q=0,
SR-H holds at c=1.

This script verifies this and counts coverage.
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


def is_witness(n, G, A, p, t_num, t_den):
    for v in G:
        if norm_int(v * t_num, t_den) * n < t_den:
            return False
    pt = (p * t_num) % t_den
    for u in A:
        if norm_int(u * pt, t_den) * n < t_den:
            return False
    return True


def chain_overlap_applies(n, W1):
    """Check if SR-H/chain-overlap sub-lemma applies."""
    if not all(math.gcd(w, n) == 1 for w in W1):
        return False
    residues = defaultdict(list)
    for w in W1:
        residues[w % n].append(w)
    for r, ws in residues.items():
        # q-values (must be consecutive starting from 0)
        q_vals = sorted(w // n for w in ws)
        if q_vals != list(range(len(q_vals))):
            return False
        if 0 not in q_vals:
            return False
    return True


def load_all():
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
    return cases


def main():
    cases = load_all()
    print(f"Total L_residual: {len(cases)}\n")

    coverage = {
        'SR (W2=empty)': 0,
        'SR-H/small (W1 in [1,n-1])': 0,
        'SR-H/chain-overlap': 0,
        'Lemma A (2n-sym pair)': 0,
        'residual analytical': 0,
    }
    chain_overlap_verified = 0
    residuals = []

    for c in cases:
        n, G, A, p = c['n'], c['G'], c['A'], c['p']
        W, W1, W2 = w1_decomp(n, G, A, p)
        all_coprime = all(math.gcd(w, n) == 1 for w in W1)

        if not W2:
            coverage['SR (W2=empty)'] += 1
            continue
        if all_coprime and all(w < n for w in W1):
            coverage['SR-H/small (W1 in [1,n-1])'] += 1
            continue
        if all_coprime and chain_overlap_applies(n, W1):
            coverage['SR-H/chain-overlap'] += 1
            # Verify
            if any(is_witness(n, G, A, p, n * k + 1, n * n) for k in range(n)):
                chain_overlap_verified += 1
            continue
        if len(W1) == 2 and all_coprime and (W1[0] + W1[1]) % (2 * n) == 0:
            coverage['Lemma A (2n-sym pair)'] += 1
            continue
        coverage['residual analytical'] += 1
        if len(residuals) < 10:
            residuals.append(c)

    print("Coverage:")
    for k, v in coverage.items():
        print(f"  {k:<35} {v}")
    print(f"\nTotal closed by sub-lemmas: {sum(v for k, v in coverage.items() if k != 'residual analytical')}/{len(cases)}")
    print(f"\nSR-H/chain-overlap verified (c=1 works empirically): {chain_overlap_verified}/{coverage['SR-H/chain-overlap']}")
    print()

    if residuals:
        print(f"Sample analytical residuals (first {min(10, len(residuals))}):")
        for c in residuals:
            n, G, A, p = c['n'], c['G'], c['A'], c['p']
            W, W1, W2 = w1_decomp(n, G, A, p)
            all_cop = all(math.gcd(w, n) == 1 for w in W1)
            residues = defaultdict(list)
            for w in W1:
                residues[w % n].append(w // n)
            qstr = ', '.join(f"r={r}: q={sorted(qs)}" for r, qs in sorted(residues.items()))
            print(f"  n={n} W1={W1} W2={W2} all-coprime={all_cop}  {qstr}")


if __name__ == "__main__":
    main()
