"""
CORRECTED order test. Bonferroni gives ALTERNATING bounds:
  Truncate at order 1: |union| ≤ sum  (UPPER)
  Truncate at order 2: |union| ≥ sum - pair  (LOWER — doesn't prove union ≤ X)
  Truncate at order 3: |union| ≤ sum - pair + triple  (UPPER)
  Truncate at order 4: |union| ≥ sum - pair + triple - quad  (LOWER)
  Truncate at order 5: |union| ≤ sum - pair + triple - quad + quint  (UPPER)

To PROVE |union| ≤ n-1, we need an UPPER bound, so use ODD-order truncation.

For each L_residual case:
  - bound_order_1 = sum  (often >> n-1 — not enough)
  - bound_order_3 = sum - pair + triple  (tighter upper bound)
  - bound_order_5 = sum - pair + triple - quad + quint  (even tighter)
  - actual = direct |union|

Classify:
  - "trivial": bound_order_1 ≤ n-1  (sum is small)
  - "triplewise_sufficient": bound_order_1 > n-1 BUT bound_order_3 ≤ n-1
  - "5wise_required": bound_order_3 > n-1 BUT bound_order_5 ≤ n-1
  - "higher": bound_order_5 > n-1, even higher truncation needed
"""
import math
import itertools
from collections import defaultdict


def norm_int(num, den):
    return min(num % den, den - num % den)


def bad_k_for(n, w, c):
    n2 = n * n
    return {k for k in range(n) if norm_int(w * (n * k + c), n2) * n < n2}


def w1_decomp(n, G, A, p):
    W = list(G) + [p * u for u in A]
    W1 = [w for w in W if w % n != 0]
    W2 = [w // n for w in W if w % n == 0]
    return W, W1, W2


def z2_good(n, W2):
    return [c for c in range(1, n) if all((w * c) % n != 0 for w in W2)]


def pigeonhole_holds(n, G, A, p):
    LG = 1
    for v in G:
        LG = LG * v // math.gcd(LG, v)
    LA = 1
    for u in A:
        LA = LA * u // math.gcd(LA, u)
    nLG = n * LG; nLA = n * LA

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
    if not I_G or not I_A:
        return None
    shift_set = set((a * p) % nLG for a in I_G)
    band_betas = set()
    for r in shift_set:
        beta_start = (r * LA // LG) % LA
        band_betas.add(beta_start)
    return len(band_betas) + len(I_A) > n * LA


def find_witness(n, G, A, p):
    n2 = n * n
    W, W1, W2 = w1_decomp(n, G, A, p)
    if not W2:
        return None
    z2g = z2_good(n, W2)
    for c in z2g:
        bad_sets = [bad_k_for(n, w, c) for w in W1]
        bad_union = set()
        for b in bad_sets:
            bad_union |= b
        if len(bad_union) < n:
            return c, bad_union, bad_sets, W1
    return None


def bonferroni_terms(bad_sets, max_order):
    """Compute the alternating Bonferroni sums up to order max_order."""
    terms = [0] * (max_order + 1)  # terms[k] = sum over k-subsets of |intersection|
    for k in range(1, max_order + 1):
        for subset in itertools.combinations(range(len(bad_sets)), k):
            inter = bad_sets[subset[0]]
            for idx in subset[1:]:
                inter = inter & bad_sets[idx]
                if not inter:
                    break
            terms[k] += len(inter)
    return terms


def gen_lrc_shape(n, vmax, p_list, max_cases=300):
    inputs = []
    speeds = list(range(1, vmax + 1))
    for kG in range(1, n - 1):
        if len(inputs) >= max_cases:
            break
        kA = n - 1 - kG
        if kA < 1:
            continue
        for G in itertools.combinations(speeds, kG):
            if len(inputs) >= max_cases:
                break
            G = list(G)
            LG = 1
            for v in G:
                LG = LG * v // math.gcd(LG, v)
            for A in itertools.combinations(speeds, kA):
                if len(inputs) >= max_cases:
                    break
                A = list(A)
                for p in p_list:
                    if math.gcd(p, LG) != 1:
                        continue
                    W = list(G) + [p * u for u in A]
                    W2 = [w // n for w in W if w % n == 0]
                    if not W2:
                        continue
                    ph = pigeonhole_holds(n, G, A, p)
                    if ph or ph is None:
                        continue
                    if find_witness(n, G, A, p) is None:
                        continue
                    inputs.append((G, A, p))
                    if len(inputs) >= max_cases:
                        break
    return inputs


def main():
    p_list = (2, 3, 5, 7, 11, 13, 17, 19)
    test_n = [5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 22, 23]

    print(f"{'n':>3} {'#cases':>7}  {'order1':>8}  {'order3':>8}  "
          f"{'order5':>8}  {'higher':>8}  {'max_ord':>8}")
    print("(counts of cases requiring each Bonferroni truncation to prove |union| ≤ n-1)\n")

    for n in test_n:
        vmax = max(10, n // 2)
        cases = gen_lrc_shape(n, vmax, p_list, max_cases=300)
        if not cases:
            print(f"  {n:>3} {0:>7}  (none)")
            continue
        order1_count = 0
        order3_count = 0
        order5_count = 0
        higher_count = 0
        max_order_seen = 1
        for (G, A, p) in cases:
            res = find_witness(n, G, A, p)
            if res is None:
                continue
            c, union, bad_sets, W1 = res
            max_ord = min(len(W1), 7)
            terms = bonferroni_terms(bad_sets, max_ord)
            # Cumulative alternating sums (Bonferroni truncations)
            partial = 0
            min_order_satisfying = None
            for k in range(1, max_ord + 1):
                partial += (-1) ** (k + 1) * terms[k]
                if k % 2 == 1:  # odd → UPPER bound
                    if partial <= n - 1:
                        min_order_satisfying = k
                        break
            if min_order_satisfying is None:
                higher_count += 1
                if max_ord > max_order_seen:
                    max_order_seen = max_ord
                continue
            if min_order_satisfying == 1:
                order1_count += 1
            elif min_order_satisfying == 3:
                order3_count += 1
            elif min_order_satisfying == 5:
                order5_count += 1
            else:
                higher_count += 1
            max_order_seen = max(max_order_seen, min_order_satisfying)
        print(f"  {n:>3} {len(cases):>7}  {order1_count:>8}  {order3_count:>8}  "
              f"{order5_count:>8}  {higher_count:>8}  {max_order_seen:>8}")


if __name__ == "__main__":
    main()
