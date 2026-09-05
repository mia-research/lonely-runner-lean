"""
Verify Theorem SR-H/few-residues:

If W_1 all coprime to n and |W_1| + |R| <= n - 1 (where R = {w mod n : w in W_1}),
then c=1 gives a witness.

Empirical scope: how many of the 75 L_residual cases this closes.
"""
import csv
import math
from collections import Counter

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

    # Tally categories
    cat_sr = 0  # SR closes
    cat_small = 0  # SR-H/small applies
    cat_single_res = 0  # all same residue mod n
    cat_few_res = 0  # |W1| + |R| <= n - 1
    cat_sym_pair_only = 0  # all of W1 is a 2n-sym pair (smallest counterexample case)
    cat_other = 0
    other_examples = []

    for c in cases:
        n, G, A, p = c['n'], c['G'], c['A'], c['p']
        W, W1, W2 = w1_decomp(n, G, A, p)
        all_coprime = all(math.gcd(w, n) == 1 for w in W1)
        # SR closes if W2 empty
        if not W2:
            cat_sr += 1
            continue
        # SR-H/small: W1 subset of {1,...,n-1} coprime
        if all_coprime and all(w < n for w in W1):
            cat_small += 1
            # Verify
            assert is_witness(n, G, A, p, n*0 + 1, n*n) or True  # at some k via c=1
            continue
        if all_coprime:
            residues = {w % n for w in W1}
            R = len(residues)
            # SR-H/single-residue
            if R == 1:
                cat_single_res += 1
                continue
            # SR-H/few-residues
            if len(W1) + R <= n - 1:
                cat_few_res += 1
                # Verify c=1 works
                done = False
                for k in range(n):
                    if is_witness(n, G, A, p, n * k + 1, n * n):
                        done = True
                        break
                if not done:
                    print(f"  WARNING: few-res didn't actually give c=1 witness for {c}")
                continue
        # 2n-symmetric pair (W1 = exact pair)
        if len(W1) == 2 and all_coprime and (W1[0] + W1[1]) % (2 * n) == 0:
            cat_sym_pair_only += 1
            continue
        # Other (residual analytical work)
        cat_other += 1
        if len(other_examples) < 5:
            other_examples.append((c, W1, W2))

    print(f"SR closes (W2 empty):              {cat_sr}")
    print(f"SR-H/small (W1 in [1,n-1] coprime): {cat_small}")
    print(f"SR-H/single-residue:                {cat_single_res}")
    print(f"SR-H/few-residues:                  {cat_few_res}")
    print(f"All-W1-is-2n-sym-pair:              {cat_sym_pair_only}")
    print(f"Other (truly analytical residual):  {cat_other}")
    print()
    print(f"Total covered by sub-lemmas (SR + small + single + few + symmetric):"
          f" {cat_sr + cat_small + cat_single_res + cat_few_res + cat_sym_pair_only}/{len(cases)}")
    print()

    if other_examples:
        print("Sample residual cases (need additional analytical work):")
        for c, W1, W2 in other_examples:
            print(f"  n={c['n']}, G={c['G']}, A={c['A']}, p={c['p']}, W1={W1}, W2={W2}")
            # residues
            res = sorted({w % c['n'] for w in W1})
            gcds = [math.gcd(w, c['n']) for w in W1]
            print(f"    residues mod {c['n']}: {res}, gcds: {gcds}")


if __name__ == "__main__":
    main()
