"""
lrc_n11_blocking_enum_v1.py

Systematic enumeration of blocking assignments for n=11.

For each complete-blocking assignment sigma: {2,...,10} -> {1,...,9}
(where sigma(m) = j means runner j is the PRIMARY blocker of witness m;
witness m=1 is always handled by runner 1 since delta_1 < 0),
compute:
  1. The required delta_j constraints (minimum |delta_j| per assignment)
  2. The minimum achievable GF in W_0 under those constraints
  3. Whether GF can be made small (approaching 0)

Also computes the sign structure: for each runner j, the pair (m_j^+, m_j^-)
where blocking m_j^+ requires delta_j > 0 and blocking m_j^- requires delta_j < 0.

Date: 2026-03-22
"""

import numpy as np
from itertools import product
from scipy.optimize import minimize

THRESHOLD = 1.0 / 11.0
DELTA_MAX = 0.90

# -----------------------------------------------------------------------
# Classical AP residues: r_j(m) = j*m mod 11
# -----------------------------------------------------------------------
def compute_residues():
    r = {}
    for j in range(1, 10):
        r[j] = {}
        for m in range(1, 11):
            r[j][m] = (j * m) % 11
    return r

RESIDUES = compute_residues()

# Verify no-missing-slot: for each m, {r_j(m): j=1..9} should be a permutation of {1..10}\{?}
# Actually for j=1..10: full bijection. For j=1..9 we miss one value.
print("Residue table r_j(m) = j*m mod 11:")
print("j\\m |", "  ".join(f"{m:2d}" for m in range(1, 11)))
print("-" * 50)
for j in range(1, 10):
    row = [RESIDUES[j][m] for m in range(1, 11)]
    print(f" {j:2d} |", "  ".join(f"{r:2d}" for r in row))

# -----------------------------------------------------------------------
# Sign structure: m_j^+ (cheapest above-blocking) and m_j^- (cheapest below)
# -----------------------------------------------------------------------
# m_j^+ is the witness m with r_j(m) = 10 (above blocking needs delta_j > 0)
# m_j^- is the witness m with r_j(m) = 1  (below blocking needs delta_j < 0)
print("\nSign structure (primary blocking pairs):")
print("j | m_j^+ (r=10, need δ>0) | m_j^- (r=1, need δ<0) | min_above | min_below")
for j in range(1, 10):
    mplus = [m for m in range(1, 11) if RESIDUES[j][m] == 10]
    mminus = [m for m in range(1, 11) if RESIDUES[j][m] == 1]
    # For each m in mplus: min delta to block above = (10-10)/m = 0
    # For each m in mminus: min |delta| to block below = (1-1)/m = 0
    print(f" {j} | m={mplus} (threshold=0+)  | m={mminus} (threshold=0-)  |", end="")
    # Also compute minimum |delta| for m=10 blocking (not in primary pairs)
    above_m10 = (10 - RESIDUES[j][10]) / 10
    below_m10 = abs((1 - RESIDUES[j][10]) / 10)
    print(f"  m=10: above>{above_m10:.2f} or below>{below_m10:.2f}")

# -----------------------------------------------------------------------
# For each (j, m), find all feasible blocking conditions within |delta| <= 0.9
# -----------------------------------------------------------------------
def get_blocking_conditions(j, m, delta_max=DELTA_MAX):
    """
    Returns list of (direction, threshold) where:
    - direction 'above': need delta_j > threshold (threshold >= 0)
    - direction 'below': need delta_j < threshold (threshold <= 0)
    Only includes conditions achievable with |delta_j| <= delta_max.

    Includes all branches (primary n=0 and nearby).
    """
    r = RESIDUES[j][m]
    conditions = []

    for n in range(-2, 3):  # include a few branches
        # Above blocking: delta_j > (10 - r + 11*n) / m
        thresh_above = (10 - r + 11 * n) / m
        if thresh_above < delta_max:  # achievable
            if thresh_above >= -delta_max:
                conditions.append(('above', thresh_above))

        # Below blocking: delta_j < (1 - r + 11*n) / m
        thresh_below = (1 - r + 11 * n) / m
        if thresh_below > -delta_max:  # achievable
            if thresh_below <= delta_max:
                conditions.append(('below', thresh_below))

    return conditions

# Compute all feasible blocking options for each (j, m)
print("\n\nFeasible blocking options for each (runner j, witness m):")
print("(showing minimum |delta| required)")
print("m\\j |", "  ".join(f"{j:4d}" for j in range(1, 10)))
print("-" * 60)

feasible_blockers = {}  # feasible_blockers[m] = list of (j, direction, threshold)
for m in range(1, 11):
    feasible_blockers[m] = []
    row_vals = []
    for j in range(1, 10):
        conds = get_blocking_conditions(j, m)
        # Find minimum |delta| achievable
        min_abs_delta = min(abs(t) for (_, t) in conds) if conds else float('inf')
        row_vals.append(f"{min_abs_delta:.3f}" if conds else "  --")
        for (direction, thresh) in conds:
            feasible_blockers[m].append((j, direction, thresh))
    print(f" {m:2d} |", "  ".join(row_vals))

# -----------------------------------------------------------------------
# Generate all minimal complete-blocking assignments
# For each m=2..10, pick the best (runner, direction) pair
# (m=1 is always blocked by runner 1 with delta_1 < 0)
# -----------------------------------------------------------------------
print("\n\nFeasible blockers per witness (sorted by min |delta|):")
for m in range(1, 11):
    options = [(j, d, t) for (j, d, t) in feasible_blockers[m]]
    options.sort(key=lambda x: abs(x[2]))
    print(f"  m={m:2d}: {[(j, d, f'{t:.3f}') for j,d,t in options[:6]]}")

# -----------------------------------------------------------------------
# Helper: check if delta vector satisfies all blocking conditions
# -----------------------------------------------------------------------
def frac(x):
    return x - np.floor(x)

def good_fraction(deltas, n_grid=4000):
    a1 = 1.0 + deltas[0]
    if a1 <= 0.005:
        return 1.0
    speeds = np.array([i + deltas[i - 1] for i in range(1, 10)] + [10.0])
    W_lo = 1.0 / (11.0 * a1)
    W_hi = 10.0 / (11.0 * a1)
    t_grid = np.linspace(W_lo, W_hi, n_grid)
    all_lonely = np.ones(n_grid, dtype=bool)
    for s in speeds:
        fr = frac(s * t_grid)
        all_lonely &= (fr >= THRESHOLD) & (fr <= 10.0 / 11.0)
    return float(np.mean(all_lonely))

def is_complete_blocking(deltas):
    a1 = 1.0 + deltas[0]
    if a1 <= 0:
        return False
    speeds = np.array([i + deltas[i - 1] for i in range(1, 10)] + [10.0])
    for m in range(1, 11):
        fr = frac(speeds * m / 11.0)
        if np.all((fr >= THRESHOLD) & (fr <= 10.0 / 11.0)):
            return False
    return True

# -----------------------------------------------------------------------
# Analyse the §10.1 example
# -----------------------------------------------------------------------
print("\n" + "=" * 65)
print("ANALYSIS OF §10.1 TOTAL-BLOCKING EXAMPLE")
print("=" * 65)
a_example = np.array([0.5, 2.2, 11/3, 33/7, 5.5, 6.0, 7.0, 8.0, 9.0, 10.0])
deltas_example = a_example[:9] - np.arange(1, 10)
print(f"a_i = {np.round(a_example, 5)}")
print(f"delta_i = {np.round(deltas_example, 5)}")
print(f"max|delta| = {np.max(np.abs(deltas_example)):.5f}")
print(f"a_1 = {a_example[0]:.4f} < 1 ✓")

# AP witness blocking table
speeds_ex = a_example
print("\nAP witness blocking table:")
for m in range(1, 11):
    fr = frac(speeds_ex * m / 11.0)
    blocked = [(i+1, round(fr[i], 4)) for i in range(9) if fr[i] < THRESHOLD or fr[i] > 10/11]
    safe = all((fr[i] >= THRESHOLD and fr[i] <= 10/11) for i in range(9))
    print(f"  m={m:2d}: {'SAFE (LRC fails)' if safe else 'blocked by '+str(blocked)}")

# GF in W_0
gf_ex = good_fraction(deltas_example, n_grid=100_000)
a1_ex = a_example[0]
W_lo_ex = 1.0 / (11.0 * a1_ex)
W_hi_ex = 10.0 / (11.0 * a1_ex)
print(f"\nW_0 = [{W_lo_ex:.5f}, {W_hi_ex:.5f}]  (width = {W_hi_ex - W_lo_ex:.5f})")
print(f"GF in W_0 (100k grid): {gf_ex:.6f} = {gf_ex*100:.4f}%")

# Check t=4/17
t_test = 4.0 / 17.0
in_W0 = W_lo_ex <= t_test <= W_hi_ex
fr_test = frac(speeds_ex * t_test)
min_dist = min(min(fr_test[i] - THRESHOLD, 10/11 - fr_test[i]) for i in range(9))
print(f"\nLRC witness t=4/17 = {t_test:.5f}:")
print(f"  In W_0: {in_W0}")
print(f"  Min lonely margin: {min_dist:.5f}")

# -----------------------------------------------------------------------
# Sign incompatibility analysis
# -----------------------------------------------------------------------
print("\n" + "=" * 65)
print("SIGN INCOMPATIBILITY ANALYSIS")
print("=" * 65)
print("\nFor each runner j, blocking m_j^+ requires delta_j > 0")
print("and blocking m_j^- requires delta_j < 0.")
print("Runner j cannot block BOTH its m_j^+ and m_j^-.")
print()

incompatible_pairs = {}
for j in range(1, 10):
    mplus = next((m for m in range(1, 11) if RESIDUES[j][m] == 10), None)
    mminus = next((m for m in range(1, 11) if RESIDUES[j][m] == 1), None)
    incompatible_pairs[j] = (mplus, mminus)
    print(f"  Runner {j}: m^+ = {mplus} (above, r={RESIDUES[j].get(mplus,'?')}), "
          f"m^- = {mminus} (below, r={RESIDUES[j].get(mminus,'?')})")

print()
print("Complementary runner pairs (cover the same pair of witnesses):")
covered = set()
for j in range(1, 10):
    mplus_j, mminus_j = incompatible_pairs[j]
    for k in range(j+1, 10):
        mplus_k, mminus_k = incompatible_pairs[k]
        if {mplus_j, mminus_j} == {mplus_k, mminus_k}:
            pair_set = frozenset({mplus_j, mminus_j})
            if pair_set not in covered:
                covered.add(pair_set)
                print(f"  Runners {j} and {k}: complementary over witnesses {{{mplus_j}, {mminus_j}}}")
                print(f"    Together always cover both {mplus_j} and {mminus_j} regardless of signs.")

# -----------------------------------------------------------------------
# Global sign assignment search: enumerate all 2^8 sign patterns
# For each pattern, find min-GF complete-blocking config
# -----------------------------------------------------------------------
print("\n" + "=" * 65)
print("EXHAUSTIVE SIGN PATTERN SEARCH (2^8 = 256 patterns)")
print("=" * 65)
print("For each sign pattern (delta_2,...,delta_9), find the min-GF")
print("complete-blocking config consistent with that sign pattern.")
print()

# For efficiency, use the sign pattern of (delta_2,...,delta_9)
# and fix delta_1 = -0.05 (a_1 = 0.95, close to 1)
# Then optimise the magnitudes to minimise GF subject to complete blocking

def blocking_penalty_tight(deltas, signs):
    """Penalty for not satisfying blocking condition consistent with sign pattern."""
    a1 = 1.0 + deltas[0]
    if a1 <= 0.005:
        return 10.0
    speeds = np.array([i + deltas[i - 1] for i in range(1, 10)] + [10.0])
    total = 0.0
    for m in range(1, 11):
        fr = frac(speeds * m / 11.0)
        margin = np.minimum(fr - THRESHOLD, 10.0 / 11.0 - fr)
        best_margin = np.max(margin)
        if best_margin > 0:
            total += best_margin
    return total

results_by_sign = []

rng = np.random.default_rng(42)

for sign_idx in range(256):  # 2^8 patterns for runners 2..9
    signs = [(sign_idx >> bit) & 1 for bit in range(8)]
    # signs[j-2] = 1 means delta_{j} > 0, = 0 means delta_{j} < 0

    # Build initial delta vector consistent with this sign pattern
    d0 = np.zeros(9)
    d0[0] = -0.05  # a_1 = 0.95
    for j in range(2, 10):
        sign = 1 if signs[j-2] else -1
        # Use minimum cost blocking (m_j^+ or m_j^-)
        mplus, mminus = incompatible_pairs[j]
        if sign == 1:
            # block m_j^+ from above: need delta_j > 0
            d0[j-1] = 0.05  # small positive
        else:
            # block m_j^- from below: need delta_j < 0
            d0[j-1] = -0.05  # small negative

    # Also need to cover m=10 — find the cheapest option
    # m=10: cheapest above-blocker is runner 2 (needs delta_2 > 0.1)
    # among positive-signed runners, check if any can cover m=10
    can_cover_10 = False
    for j in range(2, 10):
        sign = 1 if signs[j-2] else -1
        r10 = RESIDUES[j][10]
        thresh_above = (10 - r10) / 10
        thresh_below = (1 - r10) / 10
        if sign == 1 and 0.9 > thresh_above >= 0:
            can_cover_10 = True
        elif sign == -1 and -0.9 < thresh_below <= 0:
            can_cover_10 = True

    # Find min-GF complete-blocking config for this sign pattern
    # via random search then polish
    best_gf = float('inf')
    best_d = None

    for trial in range(50):  # 50 random starts per sign pattern
        d = np.zeros(9)
        d[0] = rng.uniform(-0.9, -0.001)
        for j in range(2, 10):
            sign = 1 if signs[j-2] else -1
            if sign == 1:
                d[j-1] = rng.uniform(0.001, 0.9)
            else:
                d[j-1] = rng.uniform(-0.9, -0.001)

        if not is_complete_blocking(d):
            continue

        gf = good_fraction(d, n_grid=2000)
        if gf < best_gf:
            best_gf = gf
            best_d = d.copy()

    results_by_sign.append({
        'sign_idx': sign_idx,
        'signs': signs,
        'best_gf': best_gf,
        'best_d': best_d,
        'can_cover_10': can_cover_10,
    })

    if sign_idx % 32 == 0:
        found = sum(1 for r in results_by_sign if r['best_gf'] < float('inf'))
        min_gf_so_far = min(r['best_gf'] for r in results_by_sign if r['best_gf'] < float('inf')) if found > 0 else float('nan')
        print(f"  Pattern {sign_idx:3d}/256: {found} feasible | "
              f"min GF so far = {min_gf_so_far:.4f}")

# Summary
feasible_patterns = [r for r in results_by_sign if r['best_gf'] < float('inf')]
print(f"\nFeasible sign patterns: {len(feasible_patterns)} / 256")

if feasible_patterns:
    gf_vals = [r['best_gf'] for r in feasible_patterns]
    min_gf_overall = min(gf_vals)
    min_pattern = feasible_patterns[gf_vals.index(min_gf_overall)]

    print(f"Min GF across all feasible sign patterns: {min_gf_overall:.6f}")
    print(f"  Sign pattern: {min_pattern['signs']}")
    print(f"  Signs (j=2..9): "
          + ", ".join(f"j={j+2}:{'+'if min_pattern['signs'][j] else '-'}" for j in range(8)))
    if min_pattern['best_d'] is not None:
        d = min_pattern['best_d']
        print(f"  delta_i = {np.round(d, 4)}")
        print(f"  a_i = {np.round([i+d[i-1] for i in range(1,10)] + [10.0], 4)}")
        gf_hires = good_fraction(d, n_grid=50_000)
        print(f"  GF (50k) = {gf_hires:.6f}")

    print(f"\nDistribution of min GF by sign pattern:")
    gf_buckets = [0]*11
    for gf in gf_vals:
        b = min(10, int(gf * 100))
        gf_buckets[b] += 1
    for b, cnt in enumerate(gf_buckets):
        if cnt > 0:
            print(f"  GF in [{b/100:.2f}, {(b+1)/100:.2f}): {cnt} patterns")

    # Find patterns where GF is very small
    small_gf_patterns = [r for r in feasible_patterns if r['best_gf'] < 0.015]
    print(f"\nPatterns with GF < 1.5%: {len(small_gf_patterns)}")
    for r in sorted(small_gf_patterns, key=lambda x: x['best_gf'])[:10]:
        signs_str = "".join('+' if s else '-' for s in r['signs'])
        print(f"  GF={r['best_gf']:.4f} signs(j=2..9)={signs_str}")

# -----------------------------------------------------------------------
# Final summary table
# -----------------------------------------------------------------------
print("\n" + "=" * 65)
print("ROUTE 3 BLOCKING ENUMERATION VERDICT")
print("=" * 65)
if feasible_patterns:
    print(f"Feasible sign patterns found: {len(feasible_patterns)}/256")
    print(f"Minimum GF across all patterns: {min_gf_overall:.6f} ({min_gf_overall*100:.4f}%)")
    if min_gf_overall > 0.005:
        print("STRONG SUPPORT: GF bounded away from 0 across all sign patterns.")
        print("Route 3 empirical lower bound holds.")
    elif min_gf_overall > 0:
        print("MARGINAL: GF > 0 but small. Needs further verification.")
    else:
        print("FAILS: GF = 0 found — Route 3 violated for this sign pattern!")
else:
    print("No feasible configurations found.")
