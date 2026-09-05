"""
lrc_coverage_table_v1.py
========================
For each runner p (non-mult-10, non-mult-11), compute which isolation intervals
I_k = [(11k+1)/121, (11k+10)/121] for k=0,...,10 are intersected by the blocking
zone B(p).

B(p) = union over integers j of ((11j-1)/(11p), (11j+1)/(11p))
     = union over j of (j/p - 1/(11p), j/p + 1/(11p))

Runner p intersects I_k iff there EXISTS an integer j such that
    (j/p - 1/(11p), j/p + 1/(11p))  intersects  [(11k+1)/121, (11k+10)/121]

This holds iff  j/p ∈ ((11k+1)/121 - 1/(11p), (11k+10)/121 + 1/(11p))
i.e. j ∈ (p(11k+1)/121 - 1/11,  p(11k+10)/121 + 1/11)

We use exact fraction arithmetic throughout.
"""

from fractions import Fraction
from itertools import combinations

# Isolation intervals I_k = [(11k+1)/121, (11k+10)/121]
def isolation_interval(k):
    return (Fraction(11*k+1, 121), Fraction(11*k+10, 121))

# Check if runner p's blocking zone intersects I_k
# Returns (intersects: bool, gap_width: Fraction or None)
def runner_blocks_in_Ik(p, k):
    lo, hi = isolation_interval(k)
    # B(p) = union_j (j/p - 1/(11p), j/p + 1/(11p))
    # Runner p is blocking at t iff {p*t} in [0,1/11) union (10/11,1)
    # which is equivalent to: p*t is within 1/11 of an integer
    # i.e. dist(p*t, nearest int) < 1/11
    #
    # Over I_k = [lo, hi]:  p*t ranges over [p*lo, p*hi]
    # The blocking sub-intervals of [p*lo, p*hi] are the intervals
    # [j - 1/11, j + 1/11] intersected with [p*lo, p*hi] for each integer j.
    # Convert back to t: runner p blocks in t ∈ [(j-1/11)/p, (j+1/11)/p] ∩ I_k

    p_lo = p * lo
    p_hi = p * hi
    # integers j to check
    j_lo = int(p_lo - Fraction(1,11))
    j_hi = int(p_hi + Fraction(1,11)) + 1

    blocking_intervals = []
    for j in range(j_lo, j_hi+1):
        b_lo = Fraction(j, 1) - Fraction(1, 11)
        b_hi = Fraction(j, 1) + Fraction(1, 11)
        # intersect [b_lo/p, b_hi/p] with [lo, hi]
        bl = max(b_lo / p, lo)
        bh = min(b_hi / p, hi)
        if bh > bl:
            blocking_intervals.append((bl, bh))

    # Merge overlapping blocking intervals
    if not blocking_intervals:
        return False, hi - lo  # entire I_k is a witness gap

    blocking_intervals.sort()
    merged = [blocking_intervals[0]]
    for (a, b) in blocking_intervals[1:]:
        if a <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], b))
        else:
            merged.append([a, b])

    # Compute total blocked width and gap (isolated) width within I_k
    total_blocked = sum(b - a for (a, b) in merged)
    gap_width = (hi - lo) - total_blocked

    intersects = total_blocked > 0
    return intersects, gap_width

# Compute coverage table: for each p, which k values are covered?
def compute_coverage_table(p_list, k_range=range(11)):
    table = {}
    for p in p_list:
        covered_k = set()
        for k in k_range:
            blocks, gap = runner_blocks_in_Ik(p, k)
            if blocks:
                covered_k.add(k)
        table[p] = covered_k
    return table

# Also compute the ISOLATED width within each I_k for a given runner
def coverage_detail(p, k_range=range(11)):
    details = {}
    for k in k_range:
        blocks, gap = runner_blocks_in_Ik(p, k)
        details[k] = {'blocks': blocks, 'gap_width': gap}
    return details

# For mult-10 runners: compute gap width within each I_k
def mult10_gap_table(k_range=range(11)):
    table = {}
    for m in range(2, 11):
        p = 10 * m
        table[p] = {}
        for k in k_range:
            _, gap = runner_blocks_in_Ik(p, k)
            table[p][k] = gap
    return table

# --- Period-11 residue classification ---
# For runner p with gcd(p,11)=1, the coverage pair in {I_0,...,I_10}
# should depend only on p mod 11.

def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

def coverage_by_residue(k_range=range(11)):
    residue_map = {}
    for r in range(1, 11):  # residues 1..10
        # Pick the smallest p with p mod 11 = r, not mult-10, not mult-11
        # Try p = r, r+11, r+22, ... to find a non-mult-10
        for mult in range(0, 20):
            p = r + 11 * mult
            if p >= 2 and p % 10 != 0 and p % 11 != 0:
                break
        covered = set()
        for k in k_range:
            blocks, _ = runner_blocks_in_Ik(p, k)
            if blocks:
                covered.add(k)
        residue_map[r] = {'p': p, 'covered': covered}
    return residue_map

# --- Main output ---
if __name__ == '__main__':
    print("=" * 70)
    print("LRC Coverage Table v1 — Period-11 blocking pattern analysis")
    print("=" * 70)
    print()

    # 1. Runners 2..30 (non-mult-10, non-mult-11)
    small_runners = [p for p in range(2, 31) if p % 10 != 0 and p % 11 != 0]
    table = compute_coverage_table(small_runners)

    print("Coverage table: runner p → set of I_k (k=0..10) where B(p) intersects I_k")
    print("-" * 70)
    print(f"{'p':>4}  {'p mod 11':>8}  {'covered k values':}")
    for p in small_runners:
        r = p % 11
        cov = sorted(table[p])
        print(f"{p:>4}  {r:>8}  {cov}")
    print()

    # 2. Verify period-11 pattern: same residue → same coverage set?
    print("Residue classification (p mod 11 → coverage pair):")
    print("-" * 70)
    rmap = coverage_by_residue()
    for r in range(1, 11):
        info = rmap[r]
        print(f"  residue {r:>2}  (p={info['p']:>3}):  {sorted(info['covered'])}")
    print()

    # 3. Spot-check: verify {6,7,8,9} covers {I_1,I_2,I_5,I_7,I_8,I_9}
    print("Coverage for runners {6,7,8,9}:")
    print("-" * 70)
    union_6789 = set()
    for p in [6,7,8,9]:
        cov = table[p]
        union_6789 |= cov
        print(f"  Runner {p}: {sorted(cov)}")
    print(f"  Union {{6,7,8,9}}: {sorted(union_6789)}")
    uncovered = set(range(11)) - union_6789
    print(f"  UNCOVERED: {sorted(uncovered)}")
    print()

    # 4. Mult-10 runners: gap within each I_k
    print("Mult-10 runners — isolated gap within each I_k:")
    print("-" * 70)
    m10 = mult10_gap_table()
    header = "      " + "".join(f"  I_{k:<2}" for k in range(9))
    print(header)
    for p in sorted(m10.keys()):
        row = f"p={p:>4}:"
        for k in range(9):
            g = m10[p][k]
            if g == Fraction(9, 121):
                row += "  FULL"
            elif g == 0:
                row += "  ZERO"
            else:
                row += f" {float(g):6.4f}"
        print(row)
    print()

    # 5. Witness gap in I_3 for runner 20
    print("Detailed blocking in I_3 by runner 20:")
    print("-" * 70)
    k = 3
    lo, hi = isolation_interval(k)
    print(f"  I_3 = [{float(lo):.6f}, {float(hi):.6f}] = [{lo}, {hi}]")
    p = 20
    p_lo, p_hi = p * lo, p * hi
    print(f"  p=20: {p}*t ∈ [{float(p_lo):.4f}, {float(p_hi):.4f}]")
    # Find blocking sub-intervals within I_3
    j_lo = int(p_lo - Fraction(1, 11))
    j_hi = int(p_hi + Fraction(1, 11)) + 1
    blocking = []
    for j in range(j_lo, j_hi+1):
        bl = max(Fraction(j,1) - Fraction(1,11), p_lo)
        bh = min(Fraction(j,1) + Fraction(1,11), p_hi)
        if bh > bl:
            print(f"    j={j}: blocking t ∈ ({float(bl/p):.6f}, {float(bh/p):.6f}) = ({bl/p}, {bh/p})")
            blocking.append((bl/p, bh/p))
    # Witness gaps
    gaps = []
    prev = lo
    for (bl, bh) in sorted(blocking):
        if bl > prev:
            gaps.append((prev, bl))
        prev = bh
    if prev < hi:
        gaps.append((prev, hi))
    print(f"  Witness gaps in I_3 (runner 20 isolated AND in I_3):")
    for (a, b) in gaps:
        print(f"    ({a} = {float(a):.6f}, {b} = {float(b):.6f}), width = {b-a} = {float(b-a):.6f}")
    print()

    # 6. Verify period-11 claim: for same residue class, coverage is identical
    print("Period-11 verification: same (p mod 11) → same coverage?")
    print("-" * 70)
    all_runners = [p for p in range(2, 150) if p % 10 != 0 and p % 11 != 0]
    full_table = compute_coverage_table(all_runners)
    residue_cov = {}
    mismatch = False
    for p in all_runners:
        r = p % 11
        cov = frozenset(full_table[p])
        if r not in residue_cov:
            residue_cov[r] = cov
        elif residue_cov[r] != cov:
            print(f"  MISMATCH at p={p} (r={r}): expected {sorted(residue_cov[r])}, got {sorted(cov)}")
            mismatch = True
    if not mismatch:
        print("  CONFIRMED: coverage depends only on p mod 11 for all p in 2..149. ✓")
    print()

    # 7. The 10 coverage pairs (one per residue class)
    print("The 10 residue-class coverage pairs:")
    print("-" * 70)
    for r in range(1, 11):
        cov = sorted(residue_cov[r])
        print(f"  Residue {r:>2}:  I_k covered = {cov}")
    print()

    # 8. Can any 8-residue selection cover all of I_1..I_8?
    print("Set-cover check: can any ≤8 residue classes cover all of I_1,...,I_8?")
    print("-" * 70)
    target = frozenset(range(1, 9))  # I_1 through I_8
    residue_sets = {r: residue_cov[r] & target for r in range(1, 11)}
    print(f"  Target: {sorted(target)}")
    print()
    print("  Coverage contribution toward I_1..I_8 per residue:")
    for r in range(1, 11):
        print(f"    Residue {r:>2}: {sorted(residue_sets[r])}")
    print()

    found_cover = False
    for size in range(1, 10):
        for combo in combinations(range(1, 11), size):
            union = frozenset().union(*(residue_sets[r] for r in combo))
            if union >= target:
                print(f"  COVER FOUND: residues {combo} (size {size}) cover {sorted(union)}")
                found_cover = True
                break
        if found_cover:
            break
    if not found_cover:
        print(f"  NO cover of I_1..I_8 exists using any ≤9 residue classes.")
        print(f"  → A witness MUST exist in some I_k for k∈{{1,...,8}} for any config. ✓")
    print()

    # 9. Minimum uncovered interval: for each combination of ≤8 residues,
    #    which I_k from {1,...,8} is first uncovered?
    print("First uncovered I_k for each residue combination (size ≤ 8):")
    print("-" * 70)
    min_first_uncovered = 8
    worst_combo = None
    for size in range(1, 9):
        for combo in combinations(range(1, 11), size):
            union = frozenset().union(*(residue_sets[r] for r in combo))
            uncov = sorted(target - union)
            if uncov:
                first = uncov[0]
                if first > min_first_uncovered:
                    min_first_uncovered = first
                    worst_combo = combo
    if worst_combo:
        union = frozenset().union(*(residue_sets[r] for r in worst_combo))
        uncov = sorted(target - union)
        print(f"  Latest first-uncovered: I_{min_first_uncovered} for residues {worst_combo}")
        print(f"  Union covers: {sorted(union & target)}, uncovered: {uncov}")
    else:
        print("  All combos of ≤8 residues leave I_1..I_8 gap-free — impossible by above!")
    print()

    # 10. Summary for key configs
    print("Summary: which I_k is the witness interval for key runner sets?")
    print("-" * 70)
    test_sets = [
        ([6,7,8,9], "CCL core runners"),
        ([6,7,8,9,16], "+runner 16"),
        ([6,7,8,9,17], "+runner 17"),
        ([6,7,8,9,19], "+runner 19"),
        ([6,7,8,9,16,17,19,46], "extremal config non-mult-10"),
        ([2,3,4,5,6,7,8,9], "runners 2-9"),
        ([3,6,7,8,9,12,13,14], "another set"),
    ]
    for runners, label in test_sets:
        runners_filtered = [p for p in runners if p % 10 != 0 and p % 11 != 0]
        if not runners_filtered:
            continue
        union = set()
        for p in runners_filtered:
            if p in full_table:
                union |= (full_table[p] & set(range(1,9)))
        uncov = sorted(set(range(1,9)) - union)
        print(f"  {label}: uncovered I_k in {{1..8}} = {uncov}  (first witness: I_{uncov[0] if uncov else '?'})")
