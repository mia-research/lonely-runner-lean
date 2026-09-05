"""
Third check: Resolve the tension between 28h (n=15 needs high Bonferroni order)
and 28i (Bonferroni order is a crude proxy; structural argument might be simple).

For each n in {11, 15, 9}, sample HARD cases (|W_1| close to n-1, descending kG).
For each case, examine the structural mechanism at the witness c:

  - STRUCTURAL FACT 1 (shared-all): ∃ element k_0 in bad(w) for EVERY w ∈ W_1.
  - STRUCTURAL FACT 2 (shared-most): ∃ k_0 in bad(w) for AT LEAST |W_1| - 1 of them.
  - STRUCTURAL FACT 3 (pairwise-cover): for each k ∉ good, ∃ two runners both bad at k.
  - STRUCTURAL FACT 4 (triplewise): some k bad for 3+ runners.
  - STRUCTURAL FACT 5 (complex): none of the above; need richer combinatorial argument.

These are NOT mutually exclusive; report what holds and at what "order."

Critically: if "shared-all" holds, the proof is order-1 in structural-fact terms,
EVEN IF Bonferroni truncation needs full order. This distinguishes the two metrics.
"""
import math
import itertools
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


def gen_hard_cases(n, vmax, p_list, max_cases=20):
    """Generate hard cases (largest |W_1|) at given n. Descending-kG order."""
    cases = []
    speeds = list(range(1, vmax + 1))
    for kG in range(n - 2, 0, -1):
        if len(cases) >= max_cases:
            break
        kA = n - 1 - kG
        for G in itertools.combinations(speeds, kG):
            if len(cases) >= max_cases:
                break
            G = list(G)
            LG = 1
            for v in G:
                LG = LG * v // math.gcd(LG, v)
            for A in itertools.combinations(speeds, kA):
                if len(cases) >= max_cases:
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
                    res = find_witness(n, G, A, p)
                    if res is None:
                        continue
                    cases.append((G, A, p))
                    if len(cases) >= max_cases:
                        break
    return cases


def classify_structural(W1, bad_sets, union, n):
    """Identify what STRUCTURAL FACTS hold for this case."""
    facts = {}

    # Fact: how many elements are in EVERY bad set?
    # (= |intersection over all|)
    if bad_sets:
        all_inter = bad_sets[0].copy()
        for b in bad_sets[1:]:
            all_inter &= b
        facts['shared_all_count'] = len(all_inter)
        facts['shared_all'] = sorted(all_inter)

    # Fact: how many elements are in >= |W_1| - 1 sets?
    # Equivalent: for each k, count number of bad sets containing it.
    coverage = Counter()
    for b in bad_sets:
        for k in b:
            coverage[k] += 1
    facts['max_coverage'] = max(coverage.values()) if coverage else 0
    facts['high_coverage_elements'] = sorted([k for k, c in coverage.items() if c >= len(W1) - 1])

    # Distribution of coverage
    coverage_dist = Counter(coverage.values())
    facts['coverage_dist'] = dict(sorted(coverage_dist.items()))

    # "Simple shared-all" sufficient? If shared_all is non-empty AND
    # union = shared_all ∪ (distinct "second elements" per runner),
    # then proof is simple.
    if facts['shared_all_count'] == 1:
        k0 = facts['shared_all'][0]
        # Each bad set is {k0, other}. Are "others" distinct?
        others = []
        all_size2 = True
        for b in bad_sets:
            if k0 not in b:
                all_size2 = False
                break
            rest = b - {k0}
            if len(rest) != 1:
                all_size2 = False
                break
            others.append(next(iter(rest)))
        if all_size2:
            distinct_others = len(set(others)) == len(others)
            facts['simple_shared_argument'] = distinct_others and (1 + len(set(others))) <= n - 1
            facts['others'] = others
        else:
            facts['simple_shared_argument'] = False
    else:
        facts['simple_shared_argument'] = False

    return facts


def main():
    p_list = (2, 3, 5, 7, 11, 13, 17)
    test_n = [9, 11, 15]

    for n in test_n:
        vmax = max(10, n // 2)
        cases = gen_hard_cases(n, vmax, p_list, max_cases=10)
        print(f"\n{'='*70}")
        print(f"n = {n} — {len(cases)} hard cases (largest |W_1|)")
        print(f"{'='*70}")

        simple_count = 0
        complex_count = 0

        for i, (G, A, p) in enumerate(cases):
            res = find_witness(n, G, A, p)
            c, union, bad_sets, W1 = res
            facts = classify_structural(W1, bad_sets, union, n)

            # short description
            simple = facts.get('simple_shared_argument', False)
            sh_all = facts['shared_all_count']
            max_cov = facts['max_coverage']
            print(f"\n  Case {i+1}: G={G}, A={A}, p={p}")
            print(f"    |W_1|={len(W1)}, c={c}, |union|={len(union)}")
            print(f"    shared_all (count): {sh_all} → {facts['shared_all']}")
            print(f"    max coverage: {max_cov}, coverage dist: {facts['coverage_dist']}")
            print(f"    Simple 'shared-all + distinct seconds' argument applies: {simple}")
            if simple:
                simple_count += 1
            else:
                complex_count += 1
                # Show why it's not simple
                if sh_all == 0:
                    print(f"    → No element shared by all bad sets")
                elif sh_all > 1:
                    print(f"    → {sh_all} elements shared by all (richer structure)")
                else:
                    # sh_all == 1 but argument failed somehow
                    print(f"    → Shared element exists but bad sets aren't 'size 2 with distinct seconds'")
                    print(f"    → bad sets sizes: {[len(b) for b in bad_sets]}")

        print(f"\n  Summary at n={n}: {simple_count}/{len(cases)} simple, {complex_count}/{len(cases)} complex")


if __name__ == "__main__":
    main()
