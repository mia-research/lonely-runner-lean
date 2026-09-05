"""
Push the order test to higher n — n=17, 19, 23, 29, 31, 37, 41 (primes)
and n=18, 20, 24, 30, 32, 36, 40 (composites with rich subgroup structure).

For each n: generate as many L_residual cases as possible (with vmax tuned),
then test whether pairwise is sufficient.

This tests the user's hypothesis: at some n (e.g., 41 or large composite),
pairwise might fail.
"""
import math
import itertools
from collections import defaultdict


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


def pigeonhole_holds(n, G, A, p):
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
    if not I_G or not I_A:
        return None
    cIA = len(I_A)
    shift_set = set((a * p) % nLG for a in I_G)
    band_betas = set()
    for r in shift_set:
        beta_start = (r * LA // LG) % LA
        band_betas.add(beta_start)
    return len(band_betas) + cIA > n * LA


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


def pair_overlap_count(bad_sets):
    P = 0
    for i in range(len(bad_sets)):
        for j in range(i + 1, len(bad_sets)):
            P += len(bad_sets[i] & bad_sets[j])
    return P


def triple_overlap_count(bad_sets):
    T = 0
    for i in range(len(bad_sets)):
        for j in range(i + 1, len(bad_sets)):
            for k in range(j + 1, len(bad_sets)):
                T += len(bad_sets[i] & bad_sets[j] & bad_sets[k])
    return T


def gen_lrc_shape(n, vmax, p_list, max_cases=300):
    """Generate up to max_cases LRC-shape SR-failure inputs."""
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
    p_list = (2, 3, 5, 7, 11, 13, 17, 19, 23)
    # Test primes and composites
    test_n = [17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 29, 30, 31, 32, 36, 37, 40, 41]
    # vmax scales with n; for larger n we need larger speeds to find SR-failures
    print(f"{'n':>3} {'#cases':>7} {'pair_suff':>10} {'triple_req':>11} "
          f"{'mean_P':>8} {'mean_T':>7} {'max_T':>6} {'min_pair_bound':>15}")
    for n in test_n:
        vmax = max(10, n // 2)
        cases = gen_lrc_shape(n, vmax=vmax, p_list=p_list, max_cases=300)
        if not cases:
            print(f"  {n:>3} {0:>7}  (no L_residual found at vmax={vmax})")
            continue
        pair_suff = 0
        triple_req = 0
        Ps, Ts = [], []
        min_pair_bound = float('inf')
        for (G, A, p) in cases:
            res = find_witness(n, G, A, p)
            if res is None:
                continue
            c, union, bad_sets, W1 = res
            P = pair_overlap_count(bad_sets)
            T = triple_overlap_count(bad_sets)
            sum_sizes = sum(len(b) for b in bad_sets)
            pair_only_bound = sum_sizes - P
            min_pair_bound = min(min_pair_bound, pair_only_bound)
            Ps.append(P); Ts.append(T)
            if pair_only_bound <= n - 1:
                pair_suff += 1
            else:
                triple_req += 1
        mean_P = sum(Ps) / max(1, len(Ps))
        mean_T = sum(Ts) / max(1, len(Ts))
        max_T = max(Ts) if Ts else 0
        print(f"  {n:>3} {len(cases):>7} {pair_suff:>10} {triple_req:>11} "
              f"{mean_P:>8.1f} {mean_T:>7.1f} {max_T:>6} {min_pair_bound:>15}")


if __name__ == "__main__":
    main()
