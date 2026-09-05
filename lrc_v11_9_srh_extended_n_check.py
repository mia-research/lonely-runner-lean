"""
Extend SR/SR2 verification to L_residual at n in {7, 8} (from phase7a_extended_search.csv).
Combined with phase6 (n in {4, 5, 6}), this gives 53 + 22 = 75 L_residual cases.
"""
import csv
import math
from collections import Counter

CSV6 = "/Users/trentpalelei/Desktop/Math Ex/reports/phase6_residual_arithmetic.csv"
CSV7 = "/Users/trentpalelei/Desktop/Math Ex/reports/phase7a_extended_search.csv"


def parse_speeds(s):
    return [int(x) for x in s.split("-")]


def norm_int(num, den):
    r = num % den
    return min(r, den - r)


def is_joint_witness(n, G, A, p, t_num, t_den):
    for v in G:
        if norm_int(v * t_num, t_den) * n < t_den:
            return False
    pt_num = (p * t_num) % t_den
    for u in A:
        if norm_int(u * pt_num, t_den) * n < t_den:
            return False
    return True


def find_witness_lattice_1_over_n(n, G, A, p):
    """SR: search s in {1,...,n-1} coprime to n on lattice 1/n."""
    for s in range(1, n):
        if math.gcd(s, n) != 1:
            continue
        if is_joint_witness(n, G, A, p, s, n):
            return ('SR', s, s)
    return None


def find_witness_lattice_1_over_n2(n, G, A, p):
    """SR2: search t = (nk+c)/n^2."""
    den = n * n
    for c in range(1, n):
        for k in range(n):
            m = n * k + c
            if is_joint_witness(n, G, A, p, m, den):
                return ('SR2', (k, c), m)
    return None


def sr_hypothesis_holds(n, G, A, p):
    W = list(G) + [p * u for u in A]
    return all(w % n != 0 for w in W)


def sr2_hypothesis_holds(n, G, A, p):
    """No w in W has n^2 | w."""
    W = list(G) + [p * u for u in A]
    return all(w % (n * n) != 0 for w in W)


def load_phase6():
    rows = []
    with open(CSV6) as f:
        for r in csv.DictReader(f):
            if r['stratum'] != 'L_residual':
                continue
            rows.append({
                'n': int(r['n']),
                'G': parse_speeds(r['G_speeds']),
                'A': parse_speeds(r['A_speeds']),
                'p': int(r['p']),
            })
    return rows


def load_phase7():
    rows = []
    with open(CSV7) as f:
        for r in csv.DictReader(f):
            n = int(r['n'])
            kG = int(r['kG'])
            kA = int(r['kA'])
            if kG + kA != n - 1:
                continue
            if r['pigeonhole_holds'] not in ('0', 'False', 'false'):
                continue
            if int(r['N_joint']) <= 0:
                continue
            rows.append({
                'n': n,
                'G': parse_speeds(r['G_speeds']),
                'A': parse_speeds(r['A_speeds']),
                'p': int(r['p']),
            })
    return rows


def main():
    cases = load_phase6() + load_phase7()
    print(f"Total L_residual (phase6 + phase7a): {len(cases)}\n")
    by_n = Counter(c['n'] for c in cases)
    print(f"By n: {dict(by_n)}\n")

    sr_closed = 0
    sr2_closed = 0
    not_closed = []
    sr2_hyp_fails = []
    n_witness_examples = {}

    for c in cases:
        n, G, A, p = c['n'], c['G'], c['A'], c['p']
        if sr_hypothesis_holds(n, G, A, p):
            w = find_witness_lattice_1_over_n(n, G, A, p)
            if w:
                sr_closed += 1
                n_witness_examples.setdefault(n, ('SR', w))
                continue
            else:
                # should not happen by SR theorem
                not_closed.append(('SR-FAILURE-NO-WITNESS', c))
                continue

        # SR fails: try SR2
        if not sr2_hypothesis_holds(n, G, A, p):
            sr2_hyp_fails.append(c)
            # Try lattice 1/n^3 below
            continue

        w = find_witness_lattice_1_over_n2(n, G, A, p)
        if w:
            sr2_closed += 1
            n_witness_examples.setdefault(n, ('SR2', w))
        else:
            not_closed.append(('SR2-NO-WITNESS', c))

    print(f"SR closed:                 {sr_closed}/{len(cases)}")
    print(f"SR2 closed (1/n^2):        {sr2_closed}/{len(cases)}")
    print(f"SR2 hypothesis fails:      {len(sr2_hyp_fails)} (n^2 | w for some w)")
    print(f"Not closed:                {len(not_closed)}")
    print()

    if sr2_hyp_fails:
        print("SR2 hypothesis fails (n^2 | w):")
        for c in sr2_hyp_fails:
            W = list(c['G']) + [c['p'] * u for u in c['A']]
            bad_w = [w for w in W if w % (c['n']**2) == 0]
            print(f"  n={c['n']}, G={c['G']}, A={c['A']}, p={c['p']}, n^2-multiples in W: {bad_w}")
            # Try lattice 1/n^3
            den = c['n']**3
            found = None
            for m in range(1, den):
                if is_joint_witness(c['n'], c['G'], c['A'], c['p'], m, den):
                    found = m
                    break
            print(f"    lattice 1/n^3 witness: m={found} (out of {den-1} candidates)")
        print()

    if not_closed:
        print("Not closed:")
        for tag, c in not_closed:
            print(f"  {tag}: n={c['n']}, G={c['G']}, A={c['A']}, p={c['p']}")
        print()

    print("Witness example per n (first found):")
    for n in sorted(n_witness_examples):
        print(f"  n={n}: {n_witness_examples[n]}")


if __name__ == "__main__":
    main()
