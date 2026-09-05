"""
Verification of the SR-H order-test claims. Three checks:

CHECK 1: Bonferroni direction. For a known concrete case (n=5 W_1=[1, 3, 12]
         at c=1, |union|=4), verify each order's bound matches theory.

CHECK 2: L_residual generation consistency. Phase6 has 53 cases at n ∈ {4, 5, 6};
         my gen at the same n with comparable vmax should find a SUPERSET (it
         uses more primes) but the phase6 cases should all be in it.

CHECK 3: Sampling bias at n=11, 17. Iterate gen by DECREASING kG (so we hit
         |W_1| = n-2 cases first), see if order 1 is still 100%.
"""
import math
import itertools
import csv
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
    nLG = n * LG

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


# ---- CHECK 1: Bonferroni direction on a known case ----
def check_bonferroni_known():
    print("=" * 60)
    print("CHECK 1 — Bonferroni direction on known case")
    print("=" * 60)
    # n=5, W_1=[1,3,12] at c=1. Bad sets:
    # bad(1) = {0, 4}, bad(3) = {0, 3}, bad(12) = {1, 4}
    n = 5
    W1 = [1, 3, 12]
    c = 1
    bad_sets = [bad_k_for(n, w, c) for w in W1]
    print(f"  W_1 = {W1}, c = {c}")
    for w, b in zip(W1, bad_sets):
        print(f"  bad({w}) = {sorted(b)}")
    union = set()
    for b in bad_sets:
        union |= b
    print(f"  actual union = {sorted(union)}, size = {len(union)}")

    # Bonferroni terms
    S1 = sum(len(b) for b in bad_sets)
    S2 = 0
    for i in range(len(W1)):
        for j in range(i + 1, len(W1)):
            S2 += len(bad_sets[i] & bad_sets[j])
    S3 = 0
    for i in range(len(W1)):
        for j in range(i + 1, len(W1)):
            for k in range(j + 1, len(W1)):
                S3 += len(bad_sets[i] & bad_sets[j] & bad_sets[k])

    print(f"\n  S_1 = {S1}  (sum of sizes; UPPER bound)")
    print(f"  S_1 - S_2 = {S1 - S2}  (LOWER bound)")
    print(f"  S_1 - S_2 + S_3 = {S1 - S2 + S3}  (UPPER bound)")

    # Sanity checks:
    if S1 < len(union):
        print(f"  *** BUG: S_1 ({S1}) should be ≥ actual ({len(union)})!")
    if S1 - S2 > len(union):
        print(f"  *** BUG: S_1 - S_2 ({S1-S2}) should be ≤ actual ({len(union)})!")
    if S1 - S2 + S3 < len(union):
        print(f"  *** BUG: S_1 - S_2 + S_3 ({S1-S2+S3}) should be ≥ actual ({len(union)})!")
    if S1 - S2 + S3 == len(union):
        print(f"  ✓ Inclusion-exclusion exact at order 3 (no quadruples)")
    if S1 >= len(union) >= S1 - S2 and S1 - S2 + S3 >= len(union):
        print(f"  ✓ All Bonferroni inequalities hold correctly")


# ---- CHECK 2: L_residual generation vs phase6 ----
def check_phase6_consistency():
    print("\n" + "=" * 60)
    print("CHECK 2 — L_residual generation vs phase6 ground truth")
    print("=" * 60)
    # Load phase6 L_residual at n=5
    phase6_cases = set()
    with open("/Users/trentpalelei/Desktop/Math Ex/reports/phase6_residual_arithmetic.csv") as f:
        for r in csv.DictReader(f):
            if r['stratum'] == 'L_residual' and int(r['n']) == 5:
                G = tuple(int(x) for x in r['G_speeds'].split('-'))
                A = tuple(int(x) for x in r['A_speeds'].split('-'))
                p = int(r['p'])
                phase6_cases.add((G, A, p))
    print(f"  phase6 n=5 L_residual cases: {len(phase6_cases)}")

    # Generate independently
    gen_cases = set()
    n = 5
    p_list = (2, 3, 5, 7)  # phase6 likely used these
    speeds = list(range(1, 11))
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
                        continue
                    ph = pigeonhole_holds(n, G, A, p)
                    if ph or ph is None:
                        continue
                    if find_witness(n, G, A, p) is None:
                        continue
                    gen_cases.add((tuple(G), tuple(A), p))
    print(f"  my gen n=5 L_residual cases (vmax=10, p ∈ {p_list}): {len(gen_cases)}")

    missing = phase6_cases - gen_cases
    extra = gen_cases - phase6_cases
    print(f"  phase6 \\ gen: {len(missing)}")
    print(f"  gen \\ phase6: {len(extra)}")
    if missing:
        print("  *** Some phase6 cases NOT in my gen — investigate")
        for c in list(missing)[:5]:
            print(f"      {c}")
    else:
        print("  ✓ All phase6 cases reproduced by my gen")


# ---- CHECK 3: Reverse-order n=11 sampling ----
def check_n11_bias():
    print("\n" + "=" * 60)
    print("CHECK 3 — n=11 sampling bias (try decreasing kG first)")
    print("=" * 60)
    n = 11
    p_list = (2, 3, 5, 7, 11, 13)
    speeds = list(range(1, 11))
    # Iterate decreasing kG (start with |W_1| = n-2 = 9)
    cases = []
    for kG in range(n - 2, 0, -1):
        if len(cases) >= 300:
            break
        kA = n - 1 - kG
        for G in itertools.combinations(speeds, kG):
            if len(cases) >= 300:
                break
            G = list(G)
            LG = 1
            for v in G:
                LG = LG * v // math.gcd(LG, v)
            for A in itertools.combinations(speeds, kA):
                if len(cases) >= 300:
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
                    cases.append((G, A, p, kG))
                    if len(cases) >= 300:
                        break

    print(f"  found {len(cases)} L_residual at n=11 (decreasing-kG order)")
    if not cases:
        print("  no cases found — try larger vmax")
        return
    # Tally by kG
    from collections import Counter
    by_kG = Counter(c[3] for c in cases)
    print(f"  cases by kG: {dict(sorted(by_kG.items()))}")

    # Check Bonferroni order required
    order1 = order3 = order5 = higher = 0
    for (G, A, p, kG) in cases:
        res = find_witness(n, G, A, p)
        c_val, union, bad_sets, W1 = res
        sizes = [len(b) for b in bad_sets]
        S1 = sum(sizes)
        if S1 <= n - 1:
            order1 += 1
            continue
        # Compute up to order 5
        max_ord = min(len(W1), 7)
        Ss = [0] * (max_ord + 1)
        for k in range(1, max_ord + 1):
            for subset in itertools.combinations(range(len(W1)), k):
                inter = bad_sets[subset[0]]
                for idx in subset[1:]:
                    inter = inter & bad_sets[idx]
                    if not inter:
                        break
                Ss[k] += len(inter)
        partial = 0
        found = None
        for k in range(1, max_ord + 1):
            partial += (-1) ** (k + 1) * Ss[k]
            if k % 2 == 1 and partial <= n - 1:
                found = k
                break
        if found == 1:
            order1 += 1
        elif found == 3:
            order3 += 1
        elif found == 5:
            order5 += 1
        else:
            higher += 1
    print(f"  order 1: {order1}, order 3: {order3}, order 5: {order5}, higher: {higher}")
    print(f"  hardest case has |W_1| = {max(c[3] for c in cases)}")


if __name__ == "__main__":
    check_bonferroni_known()
    check_phase6_consistency()
    check_n11_bias()
