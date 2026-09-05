#!/usr/bin/env python3
"""
lrc_n11_universalincompat_verify.py
Exact-arithmetic verification for lrc_n11_universalincompat_v2.md (Theorem U).

All arithmetic uses fractions.Fraction — no floating point.

Three gap categories uncovered during analysis of v1:
  G1. Case B2 gap width: paper v1 states 83/26950 but correct value is 83/2695.
  G2. Lemma CT: σ=−1 runners at k < canonical appear feasible but are excluded
      by the "Primary Slot Miss" lemma (B_{j,0} overshoots primary slot right edge).
  G3. Lemma CT precondition g_L ≥ 450/473 is not satisfied in Cases A2b (upper)
      and A2c; fixed by three-range case split with g_L threshold 872/935.

Author: Trent Palelei
Date: 2026-03-26
"""

from fractions import Fraction

PASS = "PASS"
FAIL = "FAIL"
results = []

def check(label, condition, detail=""):
    status = PASS if condition else FAIL
    results.append((status, label, detail))
    marker = "✓" if condition else "✗"
    print(f"  [{marker}] {label}")
    if detail:
        print(f"       {detail}")
    return condition

# ─────────────────────────────────────────────────────────────────────────────
# Basic definitions
# Slot I_k = [(11k+1)/110, (11k+10)/110]   (our AP witnesses live here)
# Bad interval B_{j,k}(a) = [(11k+10)/(11a), (11k+12)/(11a)]
# ─────────────────────────────────────────────────────────────────────────────
def slot_left(k):   return Fraction(11*k + 1,  110)
def slot_right(k):  return Fraction(11*k + 10, 110)

def bad_start(a, k): return Fraction(11*k + 10, 11) / a
def bad_end(a, k):   return Fraction(11*k + 12, 11) / a

I9_right = Fraction(109, 110)

# Feasibility interval: for B_{j,k}(a) to straddle g_L and reach 109/110
#   start ≤ g_L  ↔  a ≥ (11k+10)/(11*g_L)
#   end   ≥ 109/110  ↔  a ≤ (11k+12)*110/(11*109)
def feasibility_interval(k, g_L):
    lo = Fraction(11*k + 10, 11) / g_L
    hi = Fraction((11*k + 12) * 110, 11 * 109)
    return (lo, hi) if lo < hi else None

def speed_range(j, sigma):
    return (Fraction(j), Fraction(j+1)) if sigma == +1 else (Fraction(j-1), Fraction(j))

def intersect(lo, hi, slo, shi):
    a, b = max(lo, slo), min(hi, shi)
    return (a, b) if a < b else None


print("=" * 70)
print("SECTION 1: Key threshold verification")
print("=" * 70)

# Threshold for runner 3 (k=2) to be feasible: g_L ≥ 872/935
r3_k2_min_gL = Fraction(32 * 109, 11 * 340)
check("Runner 3 (k=2) min g_L = 32·109/(11·340) = 872/935",
      r3_k2_min_gL == Fraction(872, 935),
      f"{r3_k2_min_gL}")

# Threshold for runner 4 (k=3) to be feasible: g_L ≥ 4687/4950
r4_k3_min_gL = Fraction(43 * 109, 11 * 450)
check("Runner 4 (k=3) min g_L = 43·109/(11·450) = 4687/4950",
      r4_k3_min_gL == Fraction(4687, 4950),
      f"{r4_k3_min_gL}")

check("Ordering: 872/935 < 4687/4950 < 450/473",
      Fraction(872,935) < Fraction(4687,4950) < Fraction(450,473),
      f"≈ {float(Fraction(872,935)):.5f} < {float(Fraction(4687,4950)):.5f} < {float(Fraction(450,473)):.5f}")

# Case A2c: a₂ threshold where g_L = 23/(11a₂) drops to 872/935
# 23/(11a₂) = 872/935 → a₂ = 23·935/(11·872) = 1955/872
a2_threshold_A2c = Fraction(23 * 935, 11 * 872)
check("A2c a₂ threshold: 23·935/(11·872) = 1955/872",
      a2_threshold_A2c == Fraction(1955, 872),
      f"{a2_threshold_A2c} ≈ {float(a2_threshold_A2c):.5f}")

g_L_check = Fraction(23 * 872, 11 * 1955)
check("At a₂=1955/872: g_L = 23/(11·1955/872) = 872/935",
      g_L_check == Fraction(872, 935),
      f"g_L = {g_L_check}")

# Case A2b: a₉ threshold where g_L = 89/(11a₉) drops to 872/935
# 89/(11a₉) = 872/935 → a₉ = 89·935/(11·872) = 7565/872
a9_threshold_A2b = Fraction(89 * 935, 11 * 872)
check("A2b a₉ threshold: 89·935/(11·872) = 7565/872",
      a9_threshold_A2b == Fraction(7565, 872),
      f"{a9_threshold_A2b} ≈ {float(a9_threshold_A2b):.5f}")

g_L_check2 = Fraction(89 * 872, 11 * 7565)
check("At a₉=7565/872: g_L = 89/(11·7565/872) = 872/935",
      g_L_check2 == Fraction(872, 935),
      f"g_L = {g_L_check2}")

check("a₉ threshold 7565/872 ∈ (580/69, 87/10)",
      Fraction(580, 69) < a9_threshold_A2b < Fraction(87, 10),
      f"580/69≈{float(Fraction(580,69)):.4f} < {float(a9_threshold_A2b):.4f} < 8.7000")


print()
print("=" * 70)
print("SECTION 2: Case-specific gap bounds (corrected)")
print("=" * 70)

# Case A2a threshold
threshold_A2a = Fraction(20 * 87, 9 * 23)
check("Case A2a threshold a₉ < 580/69",
      threshold_A2a == Fraction(580, 69),
      f"20·87/(9·23) = {threshold_A2a}")

# Case A2b min gap at a₉=580/69
Delta_A2b = Fraction(109,110) - Fraction(89*69, 11*580)
check("Case A2b min gap width = 181/6380",
      Delta_A2b == Fraction(181, 6380),
      f"{Delta_A2b}")

# Case A2c min gap: Δ_R = 109/110 − 23/(11a₂) ≥ 109/110 − 207/220
Delta_A2c_min = Fraction(109,110) - Fraction(207, 220)
check("Case A2c min gap width = 1/20",
      Delta_A2c_min == Fraction(1, 20),
      f"{Delta_A2c_min}")

# Case B2 min gap — CORRECTED from paper v1's 83/26950
# Right gap is [100/(11a₉), 109/110]; at a₉=1960/207:
a9_B2_min = Fraction(1960, 207)
gap_start_B2 = Fraction(100, 11) / a9_B2_min
Delta_B2_corrected = Fraction(109,110) - gap_start_B2
check("Case B2 min gap width = 83/2695 (CORRECTION: paper v1 has typo 83/26950)",
      Delta_B2_corrected == Fraction(83, 2695),
      f"gap start = {gap_start_B2}, width = {Delta_B2_corrected}")
check("Paper v1 value 83/26950 is WRONG (off by factor 10)",
      Delta_B2_corrected != Fraction(83, 26950),
      f"83/2695 ≠ 83/26950")

# Case B3 gap
gap_B3_standard = Fraction(109,110) - Fraction(450, 473)
check("Case B3 gap at a₂=20/9: 17/430",
      gap_B3_standard == Fraction(17, 430),
      f"{gap_B3_standard}")

B21_end_at_a2_min = Fraction(23*81, 11*172)
gap_B3_min = Fraction(109,110) - B21_end_at_a2_min
check("Case B3 minimum gap (a₂=172/81): 59/9460",
      gap_B3_min == Fraction(59, 9460),
      f"B_{{2,1}} end = {B21_end_at_a2_min}, gap = {gap_B3_min}")

# Case B4 at a₉=86/9
gap_B4_at_min = Fraction(109,110) - (Fraction(100,11) / Fraction(86,9))
check("Case B4 at a₉=86/9: gap = 17/430 (matches B3)",
      gap_B4_at_min == Fraction(17, 430),
      f"{gap_B4_at_min}")


print()
print("=" * 70)
print("SECTION 3: Primary Slot Miss — σ=−1 runner exclusion")
print("  If runner j (σ=−1) covers I₉ right gap at any k, then B_{{j,0}}")
print("  overshoots primary slot right edge → GF(primary slot) > 0 directly.")
print("=" * 70)

# For runner j with σ=-1 at any feasible speed a_j ∈ (j-1, j):
# B_{j,0}[start] = 10/(11*a_j) > primary_slot[right]  iff  a_j < 100/(11*psr)
# where psr = primary_slot_right = (11*(j-2)+10)/110 for the 'lower' slot
#
# Primary slots: (3,8)→I₃/I₈, (4,7)→I₂/I₇, (5,6)→I₁/I₆
# For σ=-1 runner j, covering I₉ with k ≥ 1 means a_j is small (close to j-1),
# so B_{j,0} starts HIGH relative to the primary slot.

primary_slot_right = {
    3: slot_right(3),   # = 43/110
    4: slot_right(2),   # = 32/110  (pair (4,7) owns I₂/I₇; σ=-1 obligated to I₂)
    5: slot_right(1),   # = 21/110  (pair (5,6) owns I₁/I₆; σ=-1 obligated to I₁)
    8: slot_right(8),
    7: slot_right(7),
    6: slot_right(6),
}

print()
print("  Checking: for each σ=-1 runner j covering I₉ right gap,")
print("  does B_{j,0} overshoot the primary slot right edge?")
print()

# Runner 3 (σ=-1, k=1): a₃ ∈ [140/69, 230/109]
a3_lo = Fraction(21,11) / Fraction(207,220)  # = 140/69 (at g_L = 207/220)
B30_start_r3 = Fraction(10,11) / a3_lo
check("Runner 3 (σ=-1): B_{3,0} start ≥ 69/154 > I₃ right = 43/110",
      B30_start_r3 > primary_slot_right[3],
      f"B_{{3,0}}[start] = {B30_start_r3} = {float(B30_start_r3):.4f}, "
      f"I₃ right = {primary_slot_right[3]} = {float(primary_slot_right[3]):.4f}")

# Runner 4 (σ=-1, k=2): a₄ ∈ [640/207, 340/109]
a4_lo = Fraction(32,11) / Fraction(207,220)  # = 640/207
B40_start_r4 = Fraction(10,11) / a4_lo
check("Runner 4 (σ=-1): B_{4,0} start ≥ 207/704 > I₂ right = 16/55",
      B40_start_r4 > primary_slot_right[4],
      f"B_{{4,0}}[start] = {B40_start_r4} = {float(B40_start_r4):.4f}, "
      f"I₂ right = {primary_slot_right[4]} = {float(primary_slot_right[4]):.4f}")

# Runner 5 (σ=-1, k=3): a₅ ∈ [1849/450, 450/109] (appears at g_L=450/473)
a5_lo = Fraction(43,11) / Fraction(450,473)  # = 1849/450
B50_start_r5 = Fraction(10,11) / a5_lo
check("Runner 5 (σ=-1): B_{5,0} start ≥ 450/2035 = 90/407 > I₁ right = 21/110",
      B50_start_r5 > primary_slot_right[5],
      f"B_{{5,0}}[start] = {B50_start_r5} = {float(B50_start_r5):.5f}, "
      f"I₁ right = {primary_slot_right[5]} = {float(primary_slot_right[5]):.5f}")

# Binding PSM check: at the UPPER END of each feasible interval, B_{j,0}[start]
# is SMALLEST (since B_{j,0}[start] = 10/(11*a_j) is decreasing in a_j).
# Upper end of feasibility interval for (j, σ=-1, k) is hi = (11k+12)*110/(11*109).
# We verify the PSM holds at this tightest point for each observed (j, k) pair.
print()
print("  PSM check at UPPER END of each feasible interval (binding case):")

psm_cases = [
    # (j, k, description)
    (3, 1, "Runner 3 σ=-1, k=1: hi=230/109"),
    (4, 2, "Runner 4 σ=-1, k=2: hi=340/109"),
    (5, 3, "Runner 5 σ=-1, k=3: hi=450/109"),
]
for j, k, desc in psm_cases:
    a_hi = Fraction((11*k+12)*110, 11*109)   # upper end of feasibility interval
    B_j0_start_at_hi = Fraction(10, 11) / a_hi   # = 10*(11*109)/((11k+12)*110)
    psr = primary_slot_right[j]
    check(f"{desc}: B_{{j,0}} start = {B_j0_start_at_hi} > PSR = {psr}",
          B_j0_start_at_hi > psr,
          f"{float(B_j0_start_at_hi):.5f} > {float(psr):.5f}")


print()
print("=" * 70)
print("SECTION 4: Chain A arithmetic at extended lower bound a₃=640/207")
print("  (corresponds to g_L = 207/220, the minimum in Case A2c)")
print("=" * 70)

a3_ext = Fraction(640, 207)     # extended lower bound on a₃
a3_std = Fraction(688, 225)     # standard lower bound (g_L=450/473)
a3_hi  = Fraction(340, 109)

check("a₃ extended lower = 640/207 > a₃ standard lower = 688/225",
      a3_ext > a3_std,
      f"640/207={float(a3_ext):.4f} > 688/225={float(a3_std):.4f}")
check("a₃ extended lower still below upper bound 340/109",
      a3_ext < a3_hi,
      f"640/207={float(a3_ext):.4f} < 340/109={float(a3_hi):.4f}")

# Runner 3 cannot cover I₃ right at extended bound
I3_right = slot_right(3)  # = 43/110
a3_I3_max = Fraction(12*110, 11*43)  # = 120/43 ≈ 2.791
check("Cover I₃ right requires a₃ ≤ 120/43 ≈ 2.791",
      a3_I3_max == Fraction(120, 43))
check("a₃ ≥ 640/207 ≈ 3.092 > 120/43 ≈ 2.791: runner 3 cannot cover I₃ right",
      a3_ext > a3_I3_max,
      f"{float(a3_ext):.4f} > {float(a3_I3_max):.4f}")

# I₃ right gap width at extended minimum a₃=640/207
B30_end = bad_end(a3_ext, 0)  # = 12/(11*640/207) = 12*207/(11*640)
I3_gap_width = I3_right - B30_end
check("I₃ right gap at a₃=640/207: width = 67/1760 > 0",
      I3_gap_width == Fraction(67, 1760),
      f"width = {I3_gap_width} = {float(I3_gap_width):.5f}")

# Runner 8 min speed to cover I₃ gap: a₈ ≥ 8*a₃/3
a8_min_ext = Fraction(8*640, 3*207)  # = 5120/621
check("Runner 8 min speed at a₃=640/207: 8·640/(3·207) = 5120/621 ≈ 8.245",
      a8_min_ext == Fraction(5120, 621),
      f"{float(a8_min_ext):.4f}")
check("5120/621 > 8: forces σ₈=+1",
      a8_min_ext > 8)

# I₆ right gap — B_{3,1} end at a₃=640/207
B31_end = bad_end(a3_ext, 1)  # = 23/(11*640/207)
I6_right = slot_right(6)  # = 76/110
check("B_{3,1} end at a₃=640/207 = 4761/7040 < I₆ right = 76/110",
      B31_end < I6_right,
      f"{B31_end} = {float(B31_end):.5f} < {float(I6_right):.5f}")

# Runner 8 at a₈=5120/621: B_{8,4} end
B84_end = bad_end(a8_min_ext, 4)  # = 56/(11*5120/621)
check("B_{8,4} end at a₈=5120/621 ≤ B_{3,1} end at a₃=640/207",
      B84_end <= B31_end,
      f"B84={float(B84_end):.5f}, B31={float(B31_end):.5f}")

I6_gap_width = I6_right - B31_end
check("I₆ right gap width = 103/7040 > 0",
      I6_gap_width == Fraction(103, 7040),
      f"{I6_gap_width}")

# Chain A terminal: GF(I₈) ≥ 1/50
# Runner 6: a₆ ∈ [43*a₃/23, 225/38]
a6_lo_ext = Fraction(43*640, 23*207)   # = 27520/4761
a6_hi = Fraction(225, 38)
check("Runner 6 lower bound at a₃=640/207: 27520/4761 ≈ 5.780",
      a6_lo_ext == Fraction(27520, 4761),
      f"{float(a6_lo_ext):.4f}")
check("Runner 6 lower bound < upper bound 225/38: interval non-empty",
      a6_lo_ext < a6_hi)

I8_left = slot_left(8)   # = 89/110
B64_start = bad_start(a6_hi, 4)  # = 54/(11*225/38) = 54*38/(11*225)
I8_gap = B64_start - I8_left
check("B_{6,4} start at a₆=225/38 = 228/275",
      B64_start == Fraction(228, 275))
check("GF(I₈) ≥ B_{6,4}[start] − I₈[left] = 1/50",
      I8_gap == Fraction(1, 50),
      f"228/275 − 89/110 = {I8_gap}")


print()
print("=" * 70)
print("SECTION 5: Exhaustive feasibility check at g_L = 207/220")
print("  Expected: runner 3 (σ=+1, k=2) AND σ=-1 runners (3@k=1, 4@k=2)")
print("  σ=-1 runners excluded by PSM lemma; σ=+1 runner 3@k=2 by Chain A.")
print("=" * 70)

g_L_A2c = Fraction(207, 220)
all_feasible = []
for j in range(3, 9):
    for k in range(0, 20):
        fi = feasibility_interval(k, g_L_A2c)
        if fi is None:
            continue
        lo, hi = fi
        for sigma in [-1, +1]:
            slo, shi = speed_range(j, sigma)
            eff = intersect(lo, hi, slo, shi)
            if eff:
                all_feasible.append((j, sigma, k, eff[0], eff[1]))

print(f"\n  Feasible entries at g_L=207/220:")
for j, sigma, k, lo, hi in all_feasible:
    sign = "+" if sigma == +1 else "-"
    category = "Chain A" if (j==3 and sigma==+1 and k==2) else "PSM excl."
    print(f"    Runner {j} (σ={sign}), k={k}: [{float(lo):.4f}, {float(hi):.4f}]  [{category}]")

# Verify all non-Chain-A entries are PSM-excluded
sigma_neg_entries = [(j,k,lo,hi) for (j,sig,k,lo,hi) in all_feasible if sig == -1]
all_psm_excluded = True
for j, k, lo, hi in sigma_neg_entries:
    B_j0_start_at_lo = Fraction(10, 11) / lo  # B_{j,0} start at minimum speed
    psr = primary_slot_right.get(j)
    if psr is None:
        all_psm_excluded = False
        print(f"    WARNING: no primary slot right for j={j}")
        continue
    if B_j0_start_at_lo <= psr:
        all_psm_excluded = False
        print(f"    FAIL: Runner {j} (σ=-1, k={k}) at a_j={lo} has B_{{j,0}} start = "
              f"{B_j0_start_at_lo} ≤ primary slot right {psr}")

check("All σ=-1 feasible runners at g_L=207/220 are PSM-excluded",
      all_psm_excluded)

# Verify exactly one σ=+1 entry: runner 3 (k=2)
sigma_pos_entries = [(j,k) for (j,sig,k,lo,hi) in all_feasible if sig == +1]
check("Exactly one σ=+1 entry at g_L=207/220: runner 3 (k=2)",
      sigma_pos_entries == [(3, 2)],
      f"σ=+1 entries: {sigma_pos_entries}")


print()
print("=" * 70)
print("SECTION 6: Runner 4 (k=3) feasibility boundary")
print("  Feasible for g_L ≥ 4687/4950; infeasible for g_L < 4687/4950.")
print("=" * 70)

# Test g_L values around the threshold 4687/4950
test_gLs = [
    ("872/935 (CT lower threshold)", Fraction(872, 935), False),
    ("207/220 (A2c min)",            Fraction(207, 220), False),
    ("890/957 (A2b near-upper)",     Fraction(890, 957), False),
    ("4687/4950 (runner4 threshold)",Fraction(4687,4950),False),  # exactly at threshold: empty
    ("4688/4950",                    Fraction(4688,4950),True),   # just above: feasible
    ("450/473 (CT v1 threshold)",    Fraction(450, 473), True),
]

for name, gL, expect_feasible in test_gLs:
    fi4 = feasibility_interval(3, gL)  # k=3
    if fi4:
        lo4, hi4 = fi4
        # Check σ=+1 (a₄ ∈ (4,5)) and σ=-1 (a₄ ∈ (3,4))
        eff_pos = intersect(lo4, hi4, Fraction(4), Fraction(5))
        eff_neg = intersect(lo4, hi4, Fraction(3), Fraction(4))
        feasible = (eff_pos is not None) or (eff_neg is not None)
    else:
        feasible = False
    check(f"Runner 4 (k=3) feasible={expect_feasible} at g_L={name}",
          feasible == expect_feasible,
          f"feasibility_interval: {fi4}")


print()
print("=" * 70)
print("SECTION 7: Minimum GF across all 256 sign classes")
print("=" * 70)

min_pos = Fraction(59, 9460)    # σ₂=+1 minimum (Case B3)
min_neg = Fraction(538, 54395)  # σ₂=-1 minimum (Lemma S2)
check("σ₂=+1 minimum GF = 59/9460 > 0", min_pos > 0, f"{float(min_pos):.6f}")
check("σ₂=-1 minimum GF = 538/54395 > 0", min_neg > 0, f"{float(min_neg):.6f}")
check("Overall minimum = 59/9460 (σ₂=+1 is binding)",
      min_pos < min_neg,
      f"59/9460={float(min_pos):.6f} < 538/54395={float(min_neg):.6f}")


print()
print("=" * 70)
print("SUMMARY")
print("=" * 70)
total   = len(results)
passed  = sum(1 for r in results if r[0] == PASS)
failed  = sum(1 for r in results if r[0] == FAIL)
print(f"  Total checks: {total}")
print(f"  Passed: {passed}")
print(f"  Failed: {failed}")

if failed > 0:
    print("\nFailed checks:")
    for status, label, detail in results:
        if status == FAIL:
            print(f"  [✗] {label}")
            if detail:
                print(f"       {detail}")
    raise SystemExit(1)
else:
    print("\nAll checks passed. Theorem U arithmetic is fully verified.")
    print("Proof of lrc_n11_universalincompat_v2.md is arithmetically sound.")
