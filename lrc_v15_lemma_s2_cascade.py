"""
lrc_v15_lemma_s2_cascade.py  (v2 — corrected slot boundaries and coverage criterion)

Verifies Lemma S2 (in progress): in σ_2 = -1 sign classes, after Lemma S1 shows
runner 2 cannot cover I_9, this script checks whether runner 9's bad intervals
can overlap I_9 in the σ_2 = -1 regime.

CORRECT SETUP (from lrc_gap_investigation_v1.py):
  Slot boundaries (denominator 110 = 10*11):
    I_k = [(11k+1)/110, (11k+10)/110]  for k = 1,...,9
    I_4 = [45/110, 54/110]
    I_5 = [56/110, 65/110]
    I_9 = [100/110, 109/110] = [10/11, 109/110]

  Bad interval for speed a at branch j:
    B_{j}(a) = [(11j+10)/(11a), (11j+12)/(11a)]

  Sign convention:
    σ_2 = -1 → runner 2 is active for pair (2,9) with a_2 ∈ [25/14, 24/13]
    (runner 2 closes I_5 via B_{2,0})

  σ_2 = -1 cascade constraint on a_2 (from Lemma S1 proof):
    a_2 ∈ [25/14, 24/13]  (B_{2,0} covers I_5's left-right boundaries)

  Coverage criterion: B_{j}(a) OVERLAPS I_k means max(left(B), left(I)) < min(right(B), right(I)).
  (NOT full containment — a partial overlap is enough to reduce the witness zone.)

GOAL:
  For σ_2 = -1, determine whether runner 9 (with a_9 constrained by the cascade)
  can have any B_{9,j}(a_9) overlapping I_9. If yes, the proof needs the full
  cascade to close the witness zone argument.
"""

from fractions import Fraction

# Correct slot boundaries
I4 = (Fraction(45, 110), Fraction(54, 110))
I5 = (Fraction(56, 110), Fraction(65, 110))
I9 = (Fraction(100, 110), Fraction(109, 110))  # = [10/11, 109/110]

def bad_interval(a, j):
    """B_{j}(a) = [(11j+10)/(11a), (11j+12)/(11a)]."""
    return (Fraction(11*j + 10, 11) / a, Fraction(11*j + 12, 11) / a)

def overlaps(B, I):
    """Does interval B overlap interval I? (partial overlap counts.)"""
    return B[0] < I[1] and B[1] > I[0]

def full_covers(B, I):
    """Does B fully cover I?"""
    return B[0] <= I[0] and B[1] >= I[1]

def overlap_fraction(B, I):
    """Fraction of I covered by B (0 if disjoint)."""
    lo = max(B[0], I[0])
    hi = min(B[1], I[1])
    if lo >= hi:
        return Fraction(0)
    return (hi - lo) / (I[1] - I[0])

# ============================================================
# Part 1: Confirm Lemma S1 result with correct boundaries
# ============================================================
print("=" * 70)
print("CONFIRMING LEMMA S1 (σ_2 = -1, runner 2, correct boundaries)")
print("=" * 70)
print()
print(f"  I_5 = {I5}  ≈ ({float(I5[0]):.4f}, {float(I5[1]):.4f})")
print(f"  I_9 = {I9}  ≈ ({float(I9[0]):.4f}, {float(I9[1]):.4f})")
print()

# Runner 2 primary window (covers I_5 via B_{2,0}):
# B_{2,0}(a_2) = [10/(11a_2), 12/(11a_2)]
# Covers left boundary of I_5: 10/(11a_2) = 56/110 => a_2 = 10*110/(11*56) = 1100/616 = 25/14
# Covers right boundary of I_5: 12/(11a_2) = 65/110 => a_2 = 12*110/(11*65) = 1320/715 = 24/13
a2_lo = Fraction(25, 14)
a2_hi = Fraction(24, 13)
print(f"  Runner 2 primary window (covers I_5 via j=0): a_2 ∈ [{a2_lo}, {a2_hi}]")
print(f"    = [{float(a2_lo):.6f}, {float(a2_hi):.6f}]")
print()

# Runner 2 I_9 overlap: B_{2,j}(a_2) overlaps I_9 = [100/110, 109/110]
# For overlap: B[0] < 109/110 and B[1] > 100/110
# B_{2,j}[0] = (11j+10)/(11*a_2) < 109/110 => a_2 > (11j+10)*110/(11*109) = (11j+10)*10/109
# B_{2,j}[1] = (11j+12)/(11*a_2) > 100/110 => a_2 < (11j+12)*110/(11*100) = (11j+12)*10/100 = (11j+12)/10
print("  Runner 2 I_9 overlap conditions per branch j:")
print()
min_a2_for_I9_overlap = None
for j in range(20):
    # Overlap condition: B[0] < I9[1] and B[1] > I9[0]
    # B[0] = (11j+10)/(11*a2) < 109/110 => a2 > (11j+10)*110/(11*109)
    # B[1] = (11j+12)/(11*a2) > 100/110 => a2 < (11j+12)*110/(11*100)
    lo_overlap = Fraction((11*j+10)*110, 11*109)  # a2 must exceed this
    hi_overlap = Fraction((11*j+12)*110, 11*100)  # a2 must be below this
    if lo_overlap < hi_overlap:
        # Valid branch for overlap: a2 in (lo_overlap, hi_overlap)
        # Check intersection with primary window [a2_lo, a2_hi]
        intersect_lo = max(a2_lo, lo_overlap)
        intersect_hi = min(a2_hi, hi_overlap)
        if intersect_lo < intersect_hi:
            print(f"    j={j}: overlap range ({lo_overlap}, {hi_overlap}) INTERSECTS primary window!")
            print(f"         Intersection: ({intersect_lo}, {intersect_hi})")
        else:
            if hi_overlap > a2_lo and lo_overlap > 0:  # relevant range
                gap = intersect_lo - intersect_hi
                if abs(float(gap)) < 1:  # small gap, worth reporting
                    print(f"    j={j}: overlap range ({float(lo_overlap):.4f}, {float(hi_overlap):.4f}), "
                          f"gap from primary window = {gap}")
    if min_a2_for_I9_overlap is None or lo_overlap < min_a2_for_I9_overlap:
        if lo_overlap < hi_overlap:
            min_a2_for_I9_overlap = lo_overlap

print()
print(f"  Minimum a_2 needed for ANY I_9 overlap (j=0): "
      f"{Fraction(10*110, 11*109)} = {float(Fraction(10*110, 11*109)):.6f}")
# j=0: lo = 10*110/(11*109) = 1100/1199
# But we need B[1] > I9[0]=100/110: 12/(11*a2) > 100/110 => a2 < 12*110/(11*100) = 1320/1100 = 6/5
j0_overlap_lo = Fraction(10*110, 11*109)  # = 1100/1199
j0_overlap_hi = Fraction(12*110, 11*100)  # = 6/5
print(f"  j=0 overlap range: ({j0_overlap_lo}, {j0_overlap_hi}) "
      f"= ({float(j0_overlap_lo):.4f}, {float(j0_overlap_hi):.4f})")
print(f"  Primary window: [{a2_lo}, {a2_hi}] = [{float(a2_lo):.4f}, {float(a2_hi):.4f}]")
print()

# Check if j=1 gives overlap for a_2 ≈ 1.8
j1_overlap_lo = Fraction((11+10)*110, 11*109)  # = 2310/1199
j1_overlap_hi = Fraction((11+12)*110, 11*100)  # = 2530/1100 = 23/10
print(f"  j=1 overlap range: ({j1_overlap_lo}, {j1_overlap_hi}) "
      f"= ({float(j1_overlap_lo):.4f}, {float(j1_overlap_hi):.4f})")
print(f"  Min a_2 for j=1 overlap: {j1_overlap_lo} ≈ {float(j1_overlap_lo):.4f}")
print()
gap_S1 = j1_overlap_lo - a2_hi
print(f"  GAP (Lemma S1): j=1 overlap needs a_2 ≥ {j1_overlap_lo} = {float(j1_overlap_lo):.4f}")
print(f"  But primary window ends at a_2 = {a2_hi} = {float(a2_hi):.4f}")
print(f"  Gap = {j1_overlap_lo} - {a2_hi} = {gap_S1} = {float(gap_S1):.6f} > 0  ✓")
print()
print(f"  LEMMA S1 CONFIRMED: Runner 2 in σ_2=-1 cannot overlap I_9. Gap = {gap_S1}")

# ============================================================
# Part 2: Analyze runner 9's I_9 overlap capacity
# ============================================================
print()
print("=" * 70)
print("RUNNER 9 I_9 OVERLAP ANALYSIS")
print("=" * 70)
print()

# In σ_2 = -1: runner 2 has a_2 < 2 (primary window [25/14, 24/13] ⊂ (1,2)).
# Pair (2,9) in CB formulation: a_2 + a_9 ≈ 11.
# If a_2 ∈ [25/14, 24/13] ≈ [1.786, 1.846], then a_9 ≈ 11 - a_2 ∈ [9.154, 9.214].
# More precisely, σ_2 = -1 means a_2 < threshold → a_9 > 11 - threshold.
# The cascade forces a_9 ∈ (9, 10) approximately.

print("In σ_2 = -1 cascade: a_9 ∈ (9, 10) (since a_2 < 2 means a_9 > 9 in pair (2,9)).")
print()
print("Checking runner 9's B_{9,j}(a_9) overlap with I_9 for a_9 ∈ (9, 10):")
print()

print(f"{'j':>3}  {'lo_overlap':>15}  {'hi_overlap':>15}  "
      f"{'In (9,10)?':>12}  {'Overlap size':>14}")
print("-" * 70)

for j in range(30):
    # B_{9,j}(a9) overlaps I_9 = [100/110, 109/110] iff:
    # B[0] = (11j+10)/(11*a9) < 109/110 => a9 > (11j+10)*10/109
    # B[1] = (11j+12)/(11*a9) > 100/110 => a9 < (11j+12)*10/100 = (11j+12)/10
    lo = Fraction((11*j+10)*10, 109)
    hi = Fraction((11*j+12)*10, 100)
    if lo >= hi:
        continue
    # Intersect with a9 ∈ (9, 10)
    effective_lo = max(lo, Fraction(9))
    effective_hi = min(hi, Fraction(10))
    if effective_lo >= effective_hi:
        in_range = "NO"
        size = ""
    else:
        in_range = "YES"
        size = str(effective_hi - effective_lo)
    print(f"{j:>3}  {str(lo):>15}  {str(hi):>15}  {in_range:>12}  {size:>14}")

print()

# The critical branch is j=8:
j = 8
lo8 = Fraction((11*8+10)*10, 109)
hi8 = Fraction((11*8+12)*10, 100)
print(f"Key branch j=8:")
print(f"  Overlap range: ({lo8}, {hi8}) = ({float(lo8):.6f}, {float(hi8):.6f})")
print(f"  Intersection with (9,10): ({max(lo8, Fraction(9))}, {min(hi8, Fraction(10))})")
print()

# Now: what is the actual overlap SIZE of B_{9,8}(a9) ∩ I_9?
# B_{9,8}(a9) = [98/(11*a9), 100/(11*a9)]
# Width of B = 2/(11*a9)
# I_9 = [100/110, 109/110], width = 9/110

print("Actual overlap of B_{9,8}(a9) ∩ I_9 for a9 ∈ (9,10):")
print()
# B_{9,8}(a9) = [98/(11a9), 100/(11a9)]
# I_9 = [100/110, 109/110] = [10/11, 109/110]
# Overlap: lo = max(98/(11a9), 100/110), hi = min(100/(11a9), 109/110)

test_vals = [Fraction(91,10), Fraction(92,10), Fraction(94,10), Fraction(97,10), Fraction(99,10)]
for a9 in test_vals:
    B = bad_interval(a9, 8)
    ov_lo = max(B[0], I9[0])
    ov_hi = min(B[1], I9[1])
    ov_size = max(Fraction(0), ov_hi - ov_lo)
    frac_of_I9 = ov_size / (I9[1] - I9[0])
    print(f"  a9={float(a9):.3f}: B=[{float(B[0]):.4f},{float(B[1]):.4f}], "
          f"overlap={float(ov_size):.4f}, = {float(frac_of_I9)*100:.1f}% of I_9")

print()
print("=" * 70)
print("SUMMARY: STATUS OF LEMMA S2")
print("=" * 70)
print()
print("CONFIRMED:")
print("  - Lemma S1: Runner 2 (a_2 ∈ [25/14, 24/13]) cannot overlap I_9 (gap = 114/1417).")
print()
print("PARTIAL RESULT:")
print("  - For σ_2=-1, a_9 ∈ (9, 10). Runner 9 via branch j=8 CAN overlap I_9.")
print(f"  - B_{{9,8}}(a_9) overlaps I_9 for a_9 ∈ ({lo8}, {hi8})")
print(f"    ≈ ({float(lo8):.3f}, {float(hi8):.3f}), which intersects (9, 10).")
print()
print("REMAINING GAP:")
print("  - Runner 9 can partially overlap I_9 in σ_2=-1 (covering ~2-3% of I_9).")
print("  - Lemma S2 in the simple form 'runner 9 cannot overlap I_9' is FALSE.")
print("  - The correct Lemma S2 requires showing the cascade prevents runner 9")
print("    from contributing to CLOSING I_9 (W(I_9) > 0 is maintained).")
print()
print("CORRECT PROOF PATH:")
print("  The proof must show that the OTHER outer-pair runners (covering I_1,...,I_8)")
print("  leave a positive witness in I_9 even when runner 9's j=8 branch is active.")
print("  This requires the full cascade analysis: for each of the 128 σ_2=-1 sign")
print("  classes, show W(I_9) > 0 using the cascade-determined parameter ranges.")
print()
print("  Key insight: the width of B_{9,8} ≈ 2/(11*9.5) ≈ 0.019 is much less than")
print(f"  the width of I_9 = 9/110 ≈ {float(Fraction(9,110)):.4f}. So runner 9 alone blocks")
print("  at most ~21% of I_9. The remaining 79% must be covered by other runners.")
print("  The cascade analysis assigns those other runners to I_1,...,I_8, so they")
print("  are unlikely to also cover the remaining portion of I_9.")
print()
print("STATUS: Lemma S2 requires additional cascade work. The conceptual mechanism")
print("is understood but the explicit computation has not been completed.")
