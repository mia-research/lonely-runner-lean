"""
lrc_residue_coverage_v1.py
==========================
Gap D diagnostic: For each tested Case R> configuration, check whether
the speed set {p_i mod 11} covers all of {1,...,10}.

This tests Conjecture RCT (Residue Coverage Theorem):
  "If {p_i mod 11 : i=1,...,10} = {1,...,10}, then ILE terminates."

The test has two parts:
1. Check residue coverage for all configurations in the test dataset.
2. If any config has incomplete coverage, check if ILE still succeeds.

This identifies whether residue coverage is always present (strong support
for RCT) or only sometimes (mechanism is more subtle).

Key result: if ALL 9163+ configs have full coverage, RCT is the right
level of description. If some don't, those exceptions reveal the finer structure.
"""

from fractions import Fraction
from itertools import product
import random

# ────────────────────────────────────────────────────────────────────────────
# ILE implementation (exact rational arithmetic)
# ────────────────────────────────────────────────────────────────────────────

def ile(speeds, max_level=50):
    """
    Iterated Left-Entry Construction.
    speeds: list of positive integers [p1, p2, ..., p10], p1 = 1.
    Returns (success, t_star, level) or (False, None, max_level) if exceeded.
    """
    p1 = speeds[0]
    W_lo = Fraction(1, 11 * p1)
    W_hi = Fraction(10, 11 * p1)

    # Check if t* is already a witness in W_0
    def is_isolated(t):
        for p in speeds:
            frac = (p * t) % 1
            if frac < Fraction(1, 11) or frac > Fraction(10, 11):
                return False
        return True

    def next_left_entry(p, t_cur):
        """First left re-entry time of runner p after t_cur, within W_0."""
        # {pt} in [0, 1/11): pt in [11j, 11j+1) for integer j
        # t in [j/p, (11j+1)/(11p))
        # First j s.t. j/p > t_cur: j = ceil(p * t_cur)
        pt = p * t_cur
        j = int(pt) + 1
        t_next = Fraction(j, p)
        if t_next > W_hi:
            return None
        return t_next

    def next_right_entry(p, t_cur):
        """First right re-entry time after t_cur, within W_0."""
        # {pt} in (10/11, 1): pt in (11j+10, 11j+11) for integer j
        # t in ((11j+10)/(11p), (j+1)/p)
        # Entry at t = (11j+10)/(11p) for j s.t. that > t_cur
        pt = p * t_cur
        j = int(pt)
        t_cand = Fraction(11*j + 10, 11*p)
        if t_cand <= t_cur:
            j += 1
            t_cand = Fraction(11*j + 10, 11*p)
        if t_cand > W_hi:
            return None
        return t_cand

    t = W_lo
    for level in range(max_level):
        # Check witness at current t
        if is_isolated(t):
            return True, t, level

        # Find the blocking runner with EARLIEST re-entry time
        best_t = None
        for p in speeds[1:]:  # skip p1=1 (it's always isolated in W_0)
            frac = (p * t) % 1
            if frac < Fraction(1, 11):
                # Left-blocking: next exit is (11j+1)/(11p)
                j = int(p * t)
                t_exit = Fraction(11*j + 1, 11*p)
                if W_lo <= t_exit <= W_hi:
                    if best_t is None or t_exit < best_t:
                        best_t = t_exit
            elif frac > Fraction(10, 11):
                # Right-blocking: next exit is j/p (next period start)
                j = int(p * t) + 1
                t_exit = Fraction(j, p)
                if W_lo <= t_exit <= W_hi:
                    if best_t is None or t_exit < best_t:
                        best_t = t_exit

        if best_t is None or best_t <= t:
            return False, t, level
        t = best_t

    return False, t, max_level

# ────────────────────────────────────────────────────────────────────────────
# Residue coverage check
# ────────────────────────────────────────────────────────────────────────────

def residue_coverage(speeds):
    """Returns frozenset of {p mod 11 : p in speeds}."""
    return frozenset(p % 11 for p in speeds)

def has_full_coverage(speeds):
    """True if {p mod 11 : p in speeds} = {1,...,10}."""
    return residue_coverage(speeds) == frozenset(range(1, 11))

# ────────────────────────────────────────────────────────────────────────────
# Test dataset generation
# ────────────────────────────────────────────────────────────────────────────

def gen_test_configs(n_configs=500, ratio_range=(11, 100), seed=42):
    """Generate Case R> configurations with p1=1."""
    rng = random.Random(seed)
    configs = []
    while len(configs) < n_configs:
        ratio = rng.randint(*ratio_range)
        # Random 9 distinct speeds in [2, ratio-1], none = 11, with p10 = ratio
        cands = [p for p in range(2, ratio) if p != 11]
        if len(cands) < 9:
            continue
        interior = rng.sample(cands, 9)
        interior.sort()
        speeds = [1] + interior + [ratio]
        configs.append(speeds)
    return configs

def gen_adversarial_configs():
    """Configs with known partial residue coverage."""
    # All speeds ≡ 1 mod 11: {1, 12, 23, ..., 111}
    c1 = [1, 12, 23, 34, 45, 56, 67, 78, 89, 100]
    # Missing residue 2: no runner with p ≡ 2 mod 11
    c2 = [1, 3, 4, 5, 6, 7, 8, 9, 10, 22]
    # Staircase: (1, N, N+1,...,N+8) for N=12
    c3 = [1, 12, 13, 14, 15, 16, 17, 18, 19, 20]
    return [c1, c2, c3]

# ────────────────────────────────────────────────────────────────────────────
# Main analysis
# ────────────────────────────────────────────────────────────────────────────

def analyze(configs, label=""):
    full_cov = 0
    partial_cov = 0
    full_and_success = 0
    partial_and_success = 0
    partial_examples = []

    for speeds in configs:
        cov = has_full_coverage(speeds)
        ok, t_star, level = ile(speeds)

        if cov:
            full_cov += 1
            if ok:
                full_and_success += 1
        else:
            partial_cov += 1
            missing = frozenset(range(1, 11)) - residue_coverage(speeds)
            if ok:
                partial_and_success += 1
            if len(partial_examples) < 5:
                partial_examples.append((speeds, missing, ok, t_star, level))

    total = len(configs)
    print(f"\n{'='*60}")
    print(f"Dataset: {label} ({total} configs)")
    print(f"  Full coverage   : {full_cov}/{total}  → ILE success: {full_and_success}/{full_cov}")
    print(f"  Partial coverage: {partial_cov}/{total}  → ILE success: {partial_and_success}/{partial_cov}")

    if partial_examples:
        print("\n  Partial-coverage examples:")
        for speeds, missing, ok, t_star, level in partial_examples:
            residues = sorted(residue_coverage(speeds))
            print(f"    speeds={speeds[:5]}... missing={sorted(missing)} "
                  f"ILE={'✓' if ok else '✗'} level={level}")

    return full_cov, partial_cov, full_and_success, partial_and_success

print("LRC n=11: Gap D Residue Coverage Diagnostic")
print("=" * 60)

# Dataset 1: random configs (ratio 11-100)
configs_d1 = gen_test_configs(300, ratio_range=(12, 100), seed=42)
analyze(configs_d1, "Random ratio 12-100, seed=42")

# Dataset 2: larger ratio range
configs_d2 = gen_test_configs(300, ratio_range=(12, 300), seed=99)
analyze(configs_d2, "Random ratio 12-300, seed=99")

# Dataset 3: staircase family
staircase = []
for N in range(12, 62):
    speeds = [1] + list(range(N, N+9)) + [N+9]
    staircase.append(speeds)
analyze(staircase, f"Staircase (1,N,...,N+9) for N=12..61")

# Dataset 4: adversarial (known partial coverage)
adv = gen_adversarial_configs()
analyze(adv, "Adversarial (constructed partial coverage)")

# Dataset 5: configs specifically designed to MISS residue 2
no_r2 = []
for _ in range(100):
    rng = random.Random(hash(_))
    # Speeds with no residue 2 (mod 11): use {1,3,4,5,6,7,8,9,10,0} mod 11
    cands = [p for p in range(3, 200) if p % 11 != 2 and p % 11 != 0 and p != 1]
    if len(cands) >= 9:
        interior = sorted(rng.sample(cands, 9))
        speeds = [1] + interior + [interior[-1] * 11]  # last speed = 11x
        no_r2.append(speeds)
analyze(no_r2, "Configs with no residue-2 runner (missing r=2)")

print("\n" + "="*60)
print("INTERPRETATION:")
print("  If partial_cov ≈ 0: Full coverage is universal → RCT likely true")
print("  If partial_and_success = partial_cov: ILE succeeds regardless → RCT sufficient but not necessary")
print("  If partial_and_success < partial_cov: RCT is essential → full coverage required")
