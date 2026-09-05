"""
Follow-up verification: at n=11 with |W_1|=9, what Bonferroni order is REALLY needed?
Cap was 7 — bump to full |W_1| and check specific cases.
"""
import math
import itertools


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


def full_bonferroni(bad_sets, n):
    """Compute ALL Bonferroni terms and report at every odd order."""
    k_max = len(bad_sets)
    Ss = [0] * (k_max + 1)
    for k in range(1, k_max + 1):
        for subset in itertools.combinations(range(len(bad_sets)), k):
            inter = bad_sets[subset[0]]
            for idx in subset[1:]:
                inter = inter & bad_sets[idx]
                if not inter:
                    break
            Ss[k] += len(inter)
    # Cumulative
    partial = 0
    results = []
    for k in range(1, k_max + 1):
        partial += (-1) ** (k + 1) * Ss[k]
        results.append((k, Ss[k], partial))
    return results


def main():
    # Find one n=11 case with |W_1| = 9 and report its full Bonferroni
    n = 11
    p_list = (2, 3, 5, 7, 11, 13)
    speeds = list(range(1, 11))
    found_case = None
    for kG in range(n - 2, 0, -1):
        if found_case:
            break
        kA = n - 1 - kG
        for G in itertools.combinations(speeds, kG):
            if found_case:
                break
            G = list(G)
            LG = 1
            for v in G:
                LG = LG * v // math.gcd(LG, v)
            for A in itertools.combinations(speeds, kA):
                if found_case:
                    break
                A = list(A)
                for p in p_list:
                    if math.gcd(p, LG) != 1:
                        continue
                    W = list(G) + [p * u for u in A]
                    W2 = [w // n for w in W if w % n == 0]
                    if not W2:
                        continue
                    res = find_witness(n, G, A, p)
                    if res is None:
                        continue
                    W1 = [w for w in W if w % n != 0]
                    if len(W1) == 9:
                        found_case = (G, A, p, res)
                        break

    if not found_case:
        print("No case with |W_1|=9 found")
        return
    G, A, p, (c_val, union, bad_sets, W1) = found_case
    print(f"Case: n={n}, G={G}, A={A}, p={p}")
    print(f"  W_1 = {W1}, |W_1| = {len(W1)}")
    print(f"  witness c = {c_val}, |union| = {len(union)}, union = {sorted(union)}")
    print(f"  good k's: {sorted(set(range(n)) - union)}")
    print()
    print("  Bad sets per w:")
    for w, b in zip(W1, bad_sets):
        print(f"    bad({w}) = {sorted(b)}")
    print()
    print("  FULL Bonferroni:")
    print(f"    {'k':>3} {'S_k':>8} {'truncation':>12} {'≤ n-1?':>10} {'bound type':>15}")
    results = full_bonferroni(bad_sets, n)
    for k, sk, partial in results:
        is_upper = (k % 2 == 1)
        bound_type = "UPPER" if is_upper else "lower"
        proves_union_le_n_minus_1 = is_upper and partial <= n - 1
        marker = "✓ PROVES" if proves_union_le_n_minus_1 else ""
        print(f"    {k:>3} {sk:>8} {partial:>12} {str(partial <= n - 1):>10} {bound_type:>15} {marker}")

    # Sanity: inclusion-exclusion total should equal actual
    incl_excl = sum((-1) ** (k + 1) * sk for k, sk, _ in results)
    print(f"\n  Inclusion-exclusion total: {incl_excl}, actual |union|: {len(union)}")
    if incl_excl != len(union):
        print(f"  *** BUG ***")
    else:
        print(f"  ✓ I-E sums correctly")

    # Sanity: lower bounds always ≤ |union|; upper bounds always ≥ |union|
    print("\n  Sanity on bounds:")
    for k, sk, partial in results:
        is_upper = (k % 2 == 1)
        if is_upper and partial < len(union):
            print(f"    *** BUG: order {k} upper bound {partial} < actual {len(union)} ***")
        if not is_upper and partial > len(union):
            print(f"    *** BUG: order {k} lower bound {partial} > actual {len(union)} ***")


if __name__ == "__main__":
    main()
