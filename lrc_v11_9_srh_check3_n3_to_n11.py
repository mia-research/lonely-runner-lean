"""
Run the structural-fact check from check3 over n=3..11 systematically.

For each n:
  - Generate L_residual cases with BROADER sampling (diverse G's via random
    shuffle of iteration order, and limiting per-G case count).
  - For each case, classify the structural mechanism at the witness c.
  - Tally mechanism distribution.

Classification (refined from 28j):
  STRICT_SHARED_ALL: every bad set contains a common k_0.
  SHARED_ALL_NONVANISH: every NON-EMPTY bad set contains a common k_0, with
                       some bad sets empty (boundary vanishing).
  PAIRWISE_COMPOSITIONAL: no shared-all element, but pairs of runners share
                       elements such that pairwise overlaps cover the gap.
  MULTI_MECHANISM: requires combining shared-all + cosets + boundary vanishing
                   + ... multiple distinct algebraic facts.
  IRREGULAR: doesn't fit cleanly into the above.
"""
import math
import itertools
import random
from collections import Counter, defaultdict


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


def gen_diverse(n, vmax, p_list, max_cases=60, max_per_G=4, seed=42):
    """Generate diverse L_residual cases. Shuffle G iteration order; cap per-G."""
    random.seed(seed)
    cases = []
    speeds = list(range(1, vmax + 1))

    # Enumerate (kG, G) pairs, shuffle
    Gs = []
    for kG in range(1, n - 1):
        for G in itertools.combinations(speeds, kG):
            Gs.append((kG, list(G)))
    random.shuffle(Gs)

    per_G_count = defaultdict(int)
    for kG, G in Gs:
        if len(cases) >= max_cases:
            break
        if per_G_count[tuple(G)] >= max_per_G:
            continue
        kA = n - 1 - kG
        if kA < 1:
            continue
        LG = 1
        for v in G:
            LG = LG * v // math.gcd(LG, v)
        # Also shuffle A iteration
        As = list(itertools.combinations(speeds, kA))
        random.shuffle(As)
        for A in As:
            if len(cases) >= max_cases or per_G_count[tuple(G)] >= max_per_G:
                break
            A = list(A)
            ps = list(p_list)
            random.shuffle(ps)
            for p in ps:
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
                cases.append((G, A, p))
                per_G_count[tuple(G)] += 1
                if per_G_count[tuple(G)] >= max_per_G:
                    break
    return cases


def classify(W1, bad_sets, union, n):
    """Categorize structural mechanism."""
    nonempty = [b for b in bad_sets if b]
    empty_count = len(bad_sets) - len(nonempty)

    if not nonempty:
        return 'all_empty'

    # Strict shared-all
    strict_inter = nonempty[0].copy()
    for b in nonempty[1:]:
        strict_inter &= b

    has_shared_strict = (empty_count == 0 and strict_inter)
    has_shared_nonvanish = bool(strict_inter)  # among non-empty

    # Check if bad sets are uniform-pair (each = {k0, distinct other})
    is_simple_pair = False
    if has_shared_nonvanish and len(strict_inter) == 1:
        k0 = next(iter(strict_inter))
        sizes = [len(b) for b in nonempty]
        if all(s == 2 for s in sizes):
            others = [next(iter(b - {k0})) for b in nonempty]
            if len(set(others)) == len(others):
                is_simple_pair = True

    if is_simple_pair and empty_count == 0:
        return 'STRICT_SHARED_ALL'
    if is_simple_pair and empty_count > 0:
        return 'SHARED_ALL_NONVANISH'

    if has_shared_nonvanish:
        # Some non-pair bad sets (cosets from non-coprime), but still share k0
        # among non-empty
        if empty_count == 0:
            return 'SHARED_ALL_WITH_COSETS'
        else:
            return 'MIXED_SHARED_VANISH_COSETS'

    # No shared element across non-empty. Check pair-overlap depth.
    # Count: how many elements in {0..n-1} \ union are missing?
    good_k_count = n - len(union)
    if good_k_count >= 1:
        return 'MULTI_MECHANISM'
    return 'IRREGULAR'


def main():
    p_list = (2, 3, 5, 7, 11, 13, 17, 19)
    print(f"{'n':>3} {'#cases':>7} {'avg_|W1|':>9}  Mechanism distribution")
    print("-" * 100)
    for n in range(3, 12):
        # Pick vmax to find enough cases — for small n, vmax=10 is plenty
        vmax = max(10, n + 5)
        cases = gen_diverse(n, vmax, p_list, max_cases=60, max_per_G=4)
        if not cases:
            print(f"  {n:>3} {0:>7}  (no L_residual found)")
            continue

        mech_counts = Counter()
        w1_sizes = []
        sample_per_mech = defaultdict(list)
        for (G, A, p) in cases:
            res = find_witness(n, G, A, p)
            if res is None:
                continue
            c, union, bad_sets, W1 = res
            w1_sizes.append(len(W1))
            mech = classify(W1, bad_sets, union, n)
            mech_counts[mech] += 1
            if len(sample_per_mech[mech]) < 1:
                sample_per_mech[mech].append((G, A, p, c, [sorted(b) for b in bad_sets]))

        avg_w1 = sum(w1_sizes) / max(1, len(w1_sizes))
        # Format mech distribution
        mech_str = ", ".join(f"{m}={c}" for m, c in mech_counts.most_common())
        print(f"  {n:>3} {len(cases):>7}  {avg_w1:>9.1f}  {mech_str}")

    # Now print one sample per mechanism per n
    print("\n" + "=" * 100)
    print("SAMPLE PER MECHANISM (one per n per mech)")
    print("=" * 100)
    for n in range(3, 12):
        vmax = max(10, n + 5)
        cases = gen_diverse(n, vmax, p_list, max_cases=60, max_per_G=4)
        mech_seen = {}
        for (G, A, p) in cases:
            res = find_witness(n, G, A, p)
            if res is None:
                continue
            c, union, bad_sets, W1 = res
            mech = classify(W1, bad_sets, union, n)
            if mech not in mech_seen:
                mech_seen[mech] = (G, A, p, c, W1, bad_sets, union)
        for mech, data in mech_seen.items():
            G, A, p, c, W1, bad_sets, union = data
            print(f"\n  n={n}, mech={mech}")
            print(f"    G={G}, A={A}, p={p}, c={c}")
            print(f"    W1={W1}")
            for w, b in zip(W1, bad_sets):
                d = math.gcd(w, n)
                print(f"    bad({w}) [gcd={d}] = {sorted(b)}")
            print(f"    union = {sorted(union)} (size {len(union)}/{n-1})")
            print(f"    good k = {sorted(set(range(n)) - union)}")


if __name__ == "__main__":
    main()
