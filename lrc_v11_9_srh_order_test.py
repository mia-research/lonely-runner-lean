"""
Test: at each n, what ORDER of inclusion-exclusion is required to prove
|bad-k union| < n at the empirical witness c?

For each L_residual case (and synthetic LRC-shape inputs at higher n):
  - Find witness c (Z_2-good, gives good k).
  - Compute bad-k sets per w in W_1.
  - Compute:
      pair_overlap_count P  = sum over (w_a, w_b) of |bad_a ∩ bad_b|
      triple_overlap_count T = sum over triples of |bad_a ∩ bad_b ∩ bad_c|
  - Inclusion-exclusion:
      |union| via pairs only:   2|W_1| - P    (could overestimate if triples exist)
      |union| with triples:     2|W_1| - P + T  (better estimate)
      |union| actual:           direct |bad_1 ∪ ... ∪ bad_k|
  - Verdict:
      "pairwise_sufficient": 2|W_1| - P  ≤  n - 1
      "triplewise_required": 2|W_1| - P  ≥  n   BUT  actual ≤ n - 1

Run across n = 4..16 to see where the answer transitions.

For n > 8, generate L_residual cases by exhaustive search at small parameter ranges.
"""
import csv
import math
import itertools
from collections import Counter, defaultdict

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


def is_lrc_shape(G, A, n):
    return len(G) + len(A) == n - 1


def pigeonhole_holds(n, G, A, p):
    """Phase 5 pigeonhole sub-condition: |B| + |I_A| > n L_A."""
    LG = 1
    for v in G:
        LG = LG * v // math.gcd(LG, v)
    LA = 1
    for u in A:
        LA = LA * u // math.gcd(LA, u)
    nLG = n * LG
    nLA = n * LA

    def good_cell_idx(speeds, n, L):
        result = []
        for m in range(n * L):
            ok = True
            for v in speeds:
                d = L // v
                r = (m // d) % n
                if not (1 <= r <= n - 2):
                    ok = False
                    break
            if ok:
                result.append(m)
        return result

    I_G = good_cell_idx(G, n, LG)
    I_A = good_cell_idx(A, n, LA)
    cIG = len(I_G)
    cIA = len(I_A)
    if cIG == 0 or cIA == 0:
        return None  # degenerate
    shift_set = set((a * p) % nLG for a in I_G)
    band_betas = set()
    for r in shift_set:
        beta_start = (r * LA // LG) % LA
        band_betas.add(beta_start)
    if len(band_betas) + cIA > n * LA:
        return True
    return False


def find_witness(n, G, A, p):
    """Search lattice 1/n^2 for joint witness (k, c)."""
    n2 = n * n
    W, W1, W2 = w1_decomp(n, G, A, p)
    if not W2:
        return None  # SR closes; not in residual stratum
    z2g = z2_good(n, W2)
    for c in z2g:
        bad_union = set()
        for w in W1:
            bad_union |= bad_k_for(n, w, c)
        if len(bad_union) < n:
            good_k = next(iter(set(range(n)) - bad_union))
            return c, good_k, bad_union, [bad_k_for(n, w, c) for w in W1]
    return None


def analyze_overlap_order(n, W1, bad_sets, union):
    """Compute pair, triple, quad overlap counts and inclusion-exclusion bounds."""
    sizes = [len(b) for b in bad_sets]
    sum_sizes = sum(sizes)

    pair_overlap = 0
    triple_overlap = 0
    quad_overlap = 0

    for s in itertools.combinations(range(len(W1)), 2):
        inter = bad_sets[s[0]] & bad_sets[s[1]]
        pair_overlap += len(inter)
    for s in itertools.combinations(range(len(W1)), 3):
        inter = bad_sets[s[0]] & bad_sets[s[1]] & bad_sets[s[2]]
        triple_overlap += len(inter)
    for s in itertools.combinations(range(len(W1)), 4):
        inter = bad_sets[s[0]] & bad_sets[s[1]] & bad_sets[s[2]] & bad_sets[s[3]]
        quad_overlap += len(inter)

    # Inclusion-exclusion bounds
    actual = len(union)
    pair_only = sum_sizes - pair_overlap  # may overestimate if triples exist
    pair_plus_triple = sum_sizes - pair_overlap + triple_overlap
    return {
        'sum_sizes': sum_sizes,
        'pair_overlap': pair_overlap,
        'triple_overlap': triple_overlap,
        'quad_overlap': quad_overlap,
        'actual': actual,
        'pair_only_bound': pair_only,
        'pair_plus_triple_bound': pair_plus_triple,
    }


def gen_lrc_shape_inputs(n, vmax=10, p_list=(2, 3, 5, 7, 11)):
    """Generate LRC-shape SR-failure inputs at given n."""
    inputs = []
    speeds = list(range(1, vmax + 1))
    # |G| + |A| = n - 1
    for kG in range(1, n - 1):
        kA = n - 1 - kG
        for G in itertools.combinations(speeds, kG):
            G = list(G)
            LG = 1
            for v in G:
                LG = LG * v // math.gcd(LG, v)
            for A in itertools.combinations(speeds, kA):
                A = list(A)
                for p in p_list:
                    if math.gcd(p, LG) != 1:
                        continue
                    W = list(G) + [p * u for u in A]
                    W2 = [w // n for w in W if w % n == 0]
                    if not W2:
                        continue  # SR closes
                    # check pigeonhole fails (true L_residual)
                    if pigeonhole_holds(n, G, A, p) is not False:
                        continue
                    # check has witness
                    w = find_witness(n, G, A, p)
                    if w is None:
                        continue
                    inputs.append((G, A, p))
                    if len(inputs) >= 200:
                        return inputs
    return inputs


def load_phase_cases():
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
    print("=== Pairwise vs higher-order analysis on L_residual ===\n")
    print(f"{'n':>3} {'#cases':>6} {'pair_suff':>10} {'triple_req':>11} "
          f"{'mean_P':>8} {'max_T':>6}")

    # Use phase6+7a data for n = 4..8, generate for higher n
    cases_by_n = defaultdict(list)
    for c in load_phase_cases():
        cases_by_n[c['n']].append((c['G'], c['A'], c['p']))

    # Extend by generating L_residual at n = 9..16
    for n_gen in range(9, 17):
        print(f"  generating L_residual at n={n_gen}... ", end='', flush=True)
        gen = gen_lrc_shape_inputs(n_gen, vmax=10)
        cases_by_n[n_gen] = gen
        print(f"{len(gen)} cases")

    rows = []
    for n in sorted(cases_by_n.keys()):
        cs = cases_by_n[n]
        if not cs:
            continue
        pair_suff = 0
        triple_req = 0
        pair_overlaps = []
        max_triple = 0
        for (G, A, p) in cs:
            W, W1, W2 = w1_decomp(n, G, A, p)
            w = find_witness(n, G, A, p)
            if w is None:
                continue
            c, good_k, union, bad_sets = w
            metrics = analyze_overlap_order(n, W1, bad_sets, union)
            pair_overlaps.append(metrics['pair_overlap'])
            max_triple = max(max_triple, metrics['triple_overlap'])
            if metrics['pair_only_bound'] <= n - 1:
                pair_suff += 1
            else:
                # pairwise overestimates; triples must be present
                triple_req += 1
        mean_P = sum(pair_overlaps) / max(1, len(pair_overlaps))
        print(f"  {n:>3} {len(cs):>6} {pair_suff:>10} {triple_req:>11} "
              f"{mean_P:>8.2f} {max_triple:>6}")
        rows.append((n, len(cs), pair_suff, triple_req, mean_P, max_triple))

    print()
    print("=== Summary ===")
    print("pair_suff: pairwise inclusion-exclusion already gives |union| ≤ n-1.")
    print("triple_req: pairwise overestimates ≥ n; triple+ overlap is REQUIRED.")
    print()
    if any(t > 0 for _, _, _, t, _, _ in rows):
        print("HIGHER-ORDER MECHANISM NEEDED at:")
        for n, total, ps, tr, mp, mt in rows:
            if tr > 0:
                print(f"  n={n}: {tr}/{total} cases require triplewise+ "
                      f"(mean pair-overlap = {mp:.1f}, max triple-overlap = {mt})")
    else:
        print("PAIRWISE SUFFICIENT across all tested n.")


if __name__ == "__main__":
    main()
