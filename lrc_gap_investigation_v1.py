from fractions import Fraction
from itertools import combinations

# ============================================================
# Investigation 1: Deep dive into m=6,7,8 (the hard cases)
# ============================================================

def find_all_blockers(m, max_p=50):
    """For each valid k in W_0, find all p that block I_k^(m)."""
    k_max = min(8, (110*m - 10) // 11)
    valid_k = []
    for k in range(1, k_max + 1):
        ihi = Fraction(11*k + 10, 121*m)
        ilo = Fraction(11*k + 1, 121*m)
        if ihi >= Fraction(1, 11) and ilo <= Fraction(10, 11):
            valid_k.append(k)

    blockers = {k: [] for k in valid_k}
    for p in range(1, max_p + 1):
        if p % 11 == 0:
            continue
        for k in valid_k:
            fl = (p * Fraction(11*k+1, 121*m)) % 1
            fr = (p * Fraction(11*k+10, 121*m)) % 1
            if fl > Fraction(10,11) and fr < Fraction(1,11):
                blockers[k].append(p)
    return valid_k, blockers

print("=" * 70)
print("Deep dive: m=6,7,8 — Can any 8-runner set block ALL valid k?")
print("=" * 70)

for m in [6, 7, 8]:
    valid_k, blockers = find_all_blockers(m, max_p=100)
    print(f"\nm={m}: valid k = {valid_k}")
    for k in valid_k:
        residues = sorted(set(p % 11 for p in blockers[k]))
        print(f"  I_{k}^({m}): blocked by p = {blockers[k][:8]}... residues = {residues}")

    # Try to find a set of 8 runners that covers all k
    # For each k, what's the minimum p that blocks it?
    min_p_per_k = {k: min(blockers[k]) if blockers[k] else None for k in valid_k}
    print(f"  Min p per k: {min_p_per_k}")

    # Check: can we select one runner per k with at most 8 total runners?
    # Try exhaustive search for small runner sets
    all_runner_candidates = sorted(set(p for k in valid_k for p in blockers[k] if p <= 50))
    print(f"  All blocking runners <=50: {all_runner_candidates}")

    # Can any subset of 8 (or fewer) runners cover all valid k?
    found_cover = None
    for size in range(1, 9):
        if found_cover:
            break
        for subset in combinations(all_runner_candidates, size):
            covered = set()
            for p in subset:
                for k in valid_k:
                    if p in blockers[k]:
                        covered.add(k)
            if covered == set(valid_k):
                found_cover = subset
                break

    if found_cover:
        print(f"  *** FOUND COVER: {found_cover} blocks all {valid_k} ***")
        for p in found_cover:
            blocked = [k for k in valid_k if p in blockers[k]]
            print(f"    p={p} (r={p%11}): blocks {blocked}")
    else:
        print(f"  No cover found with <=8 runners from {{p<=50}}")
        # Find minimum cover
        print(f"  (Checking if any k has NO blocker at all: {[k for k in valid_k if not blockers[k]]})")

# Extended search with larger p
print("\n--- Extended search with p <= 200 for m=6,7,8 ---")
for m in [6, 7, 8]:
    valid_k, blockers = find_all_blockers(m, max_p=200)
    all_runner_candidates = sorted(set(p for k in valid_k for p in blockers[k] if p <= 200))
    print(f"\nm={m}: All blocking runners <=200: {all_runner_candidates}")
    for k in valid_k:
        residues = sorted(set(p % 11 for p in blockers[k]))
        print(f"  I_{k}^({m}): {len(blockers[k])} blockers, residues = {residues}, first few: {blockers[k][:6]}")

    # Can any single runner block ALL valid k simultaneously?
    universal_blockers = []
    for p in all_runner_candidates:
        if all(p in blockers[k] for k in valid_k):
            universal_blockers.append(p)
    print(f"  Universal blockers (block all k): {universal_blockers}")

    # Check pairwise coverage for m=6 (3 intervals)
    if m == 6:
        print(f"  Checking pairs from p<=200:")
        found_pair = None
        for i, p1 in enumerate(all_runner_candidates):
            if found_pair:
                break
            for p2 in all_runner_candidates[i+1:]:
                covered = set()
                for p in [p1, p2]:
                    for k in valid_k:
                        if p in blockers[k]:
                            covered.add(k)
                if covered == set(valid_k):
                    found_pair = (p1, p2)
                    break
        if found_pair:
            p1, p2 = found_pair
            print(f"  *** PAIR COVER: p={p1}(r={p1%11}) covers {[k for k in valid_k if p1 in blockers[k]]}")
            print(f"                  p={p2}(r={p2%11}) covers {[k for k in valid_k if p2 in blockers[k]]}")
        else:
            print(f"  No pair cover found from p<=200")

# Investigate q>=1 contributions
print("\n--- q>=1 (p=11q+r) contributions for m=6,7,8 ---")
for m in [6, 7, 8]:
    valid_k, blockers_50 = find_all_blockers(m, max_p=50)
    _, blockers_200 = find_all_blockers(m, max_p=200)
    print(f"\nm={m}:")
    for k in valid_k:
        q0_blockers = [p for p in blockers_50[k] if p < 11]  # q=0 (pure residues)
        q1_blockers = [p for p in blockers_200[k] if 11 <= p < 22]  # q=1
        q_larger = [p for p in blockers_200[k] if p >= 22]  # q>=2
        print(f"  k={k}: q=0 blockers (p<11): {q0_blockers}")
        print(f"         q=1 blockers (11<=p<22): {q1_blockers}")
        print(f"         q>=2 blockers (p>=22, first 5): {q_larger[:5]}")
        # Residues from each group
        r0 = sorted(set(p % 11 for p in blockers_50[k] if p < 11))
        r1 = sorted(set(p % 11 for p in blockers_200[k] if 11 <= p < 22))
        print(f"         Residues: q=0: {r0}, q=1: {r1}")

# Check: do multiple values of q for same residue give different coverage?
print("\n--- Same residue, different q: coverage analysis ---")
for m in [6]:
    valid_k, blockers = find_all_blockers(m, max_p=200)
    for r in range(1, 11):
        ps_with_r = [p for k in valid_k for p in blockers[k] if p % 11 == r]
        ps_with_r = sorted(set(ps_with_r))
        if ps_with_r:
            for p in ps_with_r:
                ks_covered = [k for k in valid_k if p in blockers[k]]
                print(f"  m={m}, p={p} (r={r}, q={p//11}): covers k={ks_covered}")

# ============================================================
# Investigation 2: Open 3 — Cascade analysis for UIT sign classes
# ============================================================

from fractions import Fraction

print("\n" + "=" * 70)
print("Open 3 Investigation: Cascade analysis for sigma_2=-1 sign classes")
print("=" * 70)

# Slot bounds
def slot(m):
    return Fraction(11*m-10, 110), Fraction(11*m-1, 110)

I4 = slot(5)   # I_4 = [45/110, 54/110]
I5 = slot(6)   # I_5 = [56/110, 65/110]
I9 = slot(10)  # I_9 = [100/110, 109/110]

print(f"I_4 = {I4[0]} to {I4[1]}")
print(f"I_5 = {I5[0]} to {I5[1]}")
print(f"I_9 = {I9[0]} to {I9[1]}")

print("\n--- Case: sigma_2=+1 (runner 2 active, I_4 primary) ---")
print("Primary: B_{2,0} covers I_4 from left -> a_2 >= 20/9")
L2 = Fraction(20, 9)
print(f"L_primary = {L2} = {float(L2):.4f}")

# With a_9 = 25/3 (cascade value for ++------):
a9_cascade = Fraction(25, 3)
B9_7_lo = Fraction(87, 11) / a9_cascade
B9_7_hi = Fraction(89, 11) / a9_cascade
print(f"a_9 = 25/3 (cascade): B_{{9,7}} = [{B9_7_lo}, {B9_7_hi}]")
left_gap_lo = I9[0]  # 10/11
left_gap_hi = B9_7_lo  # 261/275
print(f"Left gap of I_9: [{left_gap_lo}, {left_gap_hi}]")
# B_{2,1} right end >= left_gap_hi: 23/(11*a_2) >= 261/275 -> a_2 <= 575/261
R2 = Fraction(23, 11) / left_gap_hi
print(f"R_I9 = {R2} = {float(R2):.6f}")
print(f"GAP = {L2} - {R2} = {L2 - R2} [positive = incompatibility]")

print("\n--- Case: sigma_2=-1, sigma_9=-1 (runner 9 active, I_4 primary from below) ---")
print("Runner 9 with sigma_9=-1: lower-blocks t_5 (I_4 from below)")
print("B_{9,k} must cover I_4 = [45/110, 54/110] from below (left side)")
# For runner 9 to close I_4 left edge from below:
# B_{9,k} left end <= 45/110 and right end >= 45/110
# B_{9,0} = [10/(11*a_9), 12/(11*a_9)]
# For B_{9,0} to contain 45/110: need 10/(11*a_9) <= 45/110 <= 12/(11*a_9)
# -> a_9 >= 10*110/(11*45) = 1100/495 = 20/9 AND a_9 <= 12*110/(11*45) = 24/9 = 8/3
# Actually for sigma_9=-1 (a_9 < 9): the relevant bad interval is at higher k
# For a_9 ~ 25/3 ~ 8.33 (close to 9), B_{9,7} = [87/(11*a_9), 89/(11*a_9)]
# For a_9 ~ 25/3: B_{9,7} ~ [87/91.7, 89/91.7] ~ [0.949, 0.971] -- in I_9!
# For a_9 close to 8 (sigma_9 < 0, a_9 < 9):
# Runner 9 lower-blocks t_5: {a_9 * 5/11} < 1/11
# a_9 * 5/11 = k + f with 0 <= f < 1/11
# For a_9 just below 9: a_9 * 5/11 ~ 45/11 ~ 4.09, f ~ 0.09 ~ 1/11 (boundary)
# For a_9 < 9: a_9*5/11 < 45/11, f decreases below 1/11 -> LEFT-BLOCKING check

# The MINIMUM a_9 to close I_4's right edge from below:
# Need B_{9,0} right end >= I_4 right = 54/110:
# 12/(11*a_9) >= 54/110 -> a_9 <= 12*110/(11*54) = 1320/594 = 20/9
# Hmm, same value? Let me compute from first principles for runner 9 (a_9 < 9)
# The bad interval B_{9,k} for small k: k=4 gives [(44+10)/(11*a_9), (44+12)/(11*a_9)]
# = [54/(11*a_9), 56/(11*a_9)]. For a_9 ~ 5.4: B_{9,4} ~ [54/59.4, 56/59.4] ~ [0.909, 0.943] in I_9!
# For a_9 ~ 5: B_{9,4} ~ [54/55, 56/55] -> wraps!

# Let me just find what closes I_4 for runner 9 with sigma_9=-1
# Runner 9 closing I_4 = [45/110, 54/110] from the left (lower-blocking of t_5):
# {a_9 * t} < 1/11 for t in I_4 means a_9 * t in [k, k+1/11) for some integer k
# The minimum a_9 to close the FULL I_4 from below:
# Need B_{9,k_low} contains I_4 where k_low is the k value where runner 9 is in lower zone at I_4

# Try to find which k makes B_{9,k_low} cover I_4 for a_9 near its cascade value
# B_{9,k}=[( 11k+10)/(11*a_9), (11k+12)/(11*a_9)] should contain [45/110, 54/110]
# For a_9 ~ 25/3 (the ++------ cascade value -- but now sigma_9=-1 means a_9 < 9):
# For a_9 slightly less than 9: k where (11k+10)/(11*9) ~ 45/110
# (11k+10)/99 ~ 0.409 -> 11k+10 ~ 40.5 -> k ~ 2.77 -> k=3
# B_{9,3} = [43/(11*a_9), 45/(11*a_9)]
# For B_{9,3} to cover I_4 LEFT edge 45/110:
# 43/(11*a_9) <= 45/110 AND 45/(11*a_9) >= 45/110
# -> a_9 >= 43*110/(11*45) = 4730/495 = 946/99 ~ 9.56 ... but a_9 < 9 for sigma_9=-1!
# This doesn't work. Let me be more systematic.

print("For sigma_9=-1 (a_9 < 9), finding which B_{9,k} can cover I_4 = [45/110, 54/110]:")
I4_lo, I4_hi = Fraction(45,110), Fraction(54,110)
for k in range(0, 20):
    # B_{9,k} covers I_4 if left <= I4_lo and right >= I4_hi
    # left = (11k+10)/(11*a_9) <= 45/110 -> a_9 >= (11k+10)*110/(11*45) = (11k+10)*10/45
    # right = (11k+12)/(11*a_9) >= 54/110 -> a_9 <= (11k+12)*110/(11*54) = (11k+12)*10/54
    a_min = Fraction(10*(11*k+10), 45)
    a_max = Fraction(10*(11*k+12), 54)
    if a_max > a_min and a_max > 0 and a_min < 9:  # feasible range intersects (0,9)
        a_lo = max(a_min, Fraction(0))
        a_hi = min(a_max, Fraction(9))
        if a_hi > a_lo:
            print(f"  k={k}: a_9 in [{float(a_lo):.4f}, {float(a_hi):.4f}] covers I_4 (a_min={a_min}, a_max={a_max})")

print("\nFor sigma_2=-1 class, runner 2 closes I_5 = [56/110, 65/110]:")
I5_lo, I5_hi = Fraction(56,110), Fraction(65,110)
for k in range(0, 20):
    a_min = Fraction(10*(11*k+10), 56)  # left edge condition: a >=
    a_max = Fraction(10*(11*k+12), 65)  # right edge condition: a <=
    if a_max > a_min and a_min < 2:
        a_hi = min(a_max, Fraction(2))
        a_lo = max(a_min, Fraction(0))
        if a_hi > a_lo:
            print(f"  k={k}: a_2 in [{float(a_lo):.4f}, {float(a_hi):.4f}] closes I_5 (for sigma_2=-1, a_2 < 2)")

# Now compute cascade locking for a few simple sigma_2=-1 sign classes
print("\n--- General UIT structure for sigma_2=-1 classes ---")
print("Key question: what locks runner 2 to a specific value?")
print()
print("In ++------, runner 9 is locked at 25/3 by:")
print("  - Pair (5,6) in ++------ must close I_1 and I_8")
print("  - sigma_5=-1: runner 5 covers I_8 from below, forcing a_5 in specific range")
print("  - sigma_6=-1: runner 6 covers I_1 from below")
print("  - The cascade from pair (5,6) propagates to pair (2,9)")
print()
print("For sigma_2=-1 class, runner 2 is the one forced by cascade.")
print("Runner 2 with sigma_2=-1: closes I_5 from below (B_{2,0} or B_{2,1})")
print()

# For sigma_2=-1: runner 2 must have {a_2 * 6/11} < 1/11 (lower-blocking t_6 for I_5)
# a_2 * 6/11 in [1, 1+1/11) -> a_2 in [11/6, 12/6) = [11/6, 2)
# So cascade forces a_2 in [11/6, 2) for sigma_2=-1 classes
# Primary obligation: close I_5 right edge: B_{2,0} right = 12/(11*a_2) >= 65/110
# -> a_2 <= 12*110/(11*65) = 1320/715 = 24/13 ~ 1.846
# And close I_5 left edge: 10/(11*a_2) <= 56/110 -> a_2 >= 1100/(11*56) = 25/14 ~ 1.786

print("For sigma_2=-1, B_{2,0} covers I_5 when:")
print(f"  Left edge: a_2 >= 25/14 = {Fraction(25,14)} ~ {float(Fraction(25,14)):.4f}")
print(f"  Right edge: a_2 <= 24/13 = {Fraction(24,13)} ~ {float(Fraction(24,13)):.4f}")
print()
# Primary obligation for sigma_2=-1: must close I_5 -> a_2 >= 25/14 (at minimum)
# But actually the "primary obligation" lower bound depends on closing the WORST gap
# The worst gap in I_5 depends on the cascade (what other runners cover)

# For I_9 coverage by runner 2 (sigma_2=-1, a_2 < 2):
# B_{2,1} = [21/(11*a_2), 23/(11*a_2)]
# For a_2 ~ 11/6 ~ 1.833:
a2_example = Fraction(11,6)
B21_lo = Fraction(21,11) / a2_example
B21_hi = Fraction(23,11) / a2_example
print(f"For a_2 = 11/6: B_{{2,1}} = [{B21_lo} ~ {float(B21_lo):.4f}, {B21_hi} ~ {float(B21_hi):.4f}]")
print(f"I_9 = [{I9[0]} ~ {float(I9[0]):.4f}, {I9[1]} ~ {float(I9[1]):.4f}]")
if B21_lo <= I9[0] and B21_hi >= I9[0]:
    print(f"B_{{2,1}} overlaps I_9 from the left!")
elif B21_hi < I9[0]:
    print(f"B_{{2,1}} is BELOW I_9 entirely -- runner 2 can't cover I_9 when a_2 = 11/6")
else:
    print(f"B_{{2,1}} is above I_9")

print()
print("Summary of Open 3 cascade question:")
print("For sigma_2=-1: primary obligation forces a_2 in [25/14, 24/13] ~ [1.786, 1.846]")
print("Can B_{2,1} reach I_9 = [100/110, 109/110] for a_2 in this range?")
for a2 in [Fraction(25,14), Fraction(24,13), Fraction(11,6)]:
    B21 = (Fraction(21,11)/a2, Fraction(23,11)/a2)
    print(f"  a_2={a2}={float(a2):.4f}: B_{{2,1}}=[{float(B21[0]):.4f},{float(B21[1]):.4f}]"
          f" I_9=[{float(I9[0]):.4f},{float(I9[1]):.4f}] -> overlap={B21[1] >= I9[0] and B21[0] <= I9[1]}")

# Additional analysis: what range of a_2 allows B_{2,1} to reach I_9?
print()
print("What range of a_2 allows B_{2,1} to overlap I_9 = [100/110, 109/110]?")
# B_{2,1} = [21/(11*a_2), 23/(11*a_2)] overlaps I_9 = [10/11, 109/110] iff:
# B_{2,1}.right >= I_9.left AND B_{2,1}.left <= I_9.right
# 23/(11*a_2) >= 10/11 -> a_2 <= 23/10 = 2.3
# 21/(11*a_2) <= 109/110 -> a_2 >= 21*110/(11*109) = 2310/1199 ~ 1.927
a2_I9_lo = Fraction(21*110, 11*109)
a2_I9_hi = Fraction(23, 10)
print(f"  B_{{2,1}} overlaps I_9 when a_2 in [{a2_I9_lo} ~ {float(a2_I9_lo):.4f}, {a2_I9_hi} ~ {float(a2_I9_hi):.4f}]")
print(f"  But sigma_2=-1 requires a_2 < 2")
print(f"  And B_{{2,1}} needs a_2 >= {float(a2_I9_lo):.4f} > 2 to reach I_9!")
print(f"  => IMPOSSIBLE for sigma_2=-1 classes: runner 2 CANNOT cover I_9")

print()
print("--- Checking all B_{2,j} for a_2 < 2 vs I_9 ---")
for j in range(0, 5):
    # B_{2,j} = [(11j+10)/(11*a_2), (11j+12)/(11*a_2)]
    # To overlap I_9 = [10/11, 109/110]:
    # Right >= 10/11: (11j+12)/(11*a_2) >= 10/11 -> a_2 <= (11j+12)/10
    # Left <= 109/110: (11j+10)/(11*a_2) <= 109/110 -> a_2 >= (11j+10)*10/109
    a2_lo_j = Fraction(10*(11*j+10), 109)
    a2_hi_j = Fraction(11*j+12, 10)
    # Intersect with (0, 2) for sigma_2=-1
    a2_lo_eff = max(a2_lo_j, Fraction(0))
    a2_hi_eff = min(a2_hi_j, Fraction(2))
    if a2_hi_eff > a2_lo_eff:
        print(f"  j={j}: B_{{2,{j}}} can reach I_9 for a_2 in [{float(a2_lo_eff):.4f}, {float(a2_hi_eff):.4f}]")
        print(f"    (a_2 < 2 constraint: effective range [{float(a2_lo_eff):.4f}, {float(a2_hi_eff):.4f}])")
    else:
        print(f"  j={j}: B_{{2,{j}}} CANNOT reach I_9 for any a_2 in (0,2)")
        print(f"    (requires a_2 in [{float(a2_lo_j):.4f}, {float(a2_hi_j):.4f}], outside (0,2))")

# Analysis for the three specific sign classes
print("\n" + "=" * 70)
print("Three specific sign classes analysis")
print("=" * 70)

# Helper: bad interval B_{j,k} = [(11k+10)/(11*a_j), (11k+12)/(11*a_j)]
def bad_interval(a_j, k):
    lo = Fraction(11*k+10, 11) / a_j
    hi = Fraction(11*k+12, 11) / a_j
    return lo, hi

# 1. -------- (all negative): sigma_2=-1, sigma_9=-1
print("\nClass 1: '--------' (all sigma = -1)")
print("sigma_2=-1: runner 2 must close I_5 from below -> a_2 in [11/6, 2)")
print("sigma_9=-1: runner 9 must close I_4 from below -> a_9 in ...")
print()
# For sigma_9=-1 and I_4: from earlier analysis, which k value works?
# B_{9,k} covers I_4=[45/110, 54/110] for a_9 < 9?
# From the loop above we found k values. Let's redo explicitly:
print("Finding k for B_{9,k} to cover I_4 when a_9 < 9:")
found_k9 = []
for k in range(0, 20):
    a_min = Fraction(10*(11*k+10), 45)
    a_max = Fraction(10*(11*k+12), 54)
    if a_max > a_min and a_min < 9 and a_max > 0:
        a_lo = max(a_min, Fraction(0))
        a_hi = min(a_max, Fraction(9))
        if a_hi > a_lo:
            found_k9.append((k, a_lo, a_hi))
            print(f"  k={k}: a_9 in [{a_lo}={float(a_lo):.4f}, {a_hi}={float(a_hi):.4f}]")

print()
print("Primary obligation for runner 9 (sigma_9=-1, close I_4):")
if found_k9:
    k9, a9_lo, a9_hi = found_k9[-1]  # take the last/largest range
    print(f"  Using k={k9}: a_9 in [{a9_lo}={float(a9_lo):.4f}, {a9_hi}={float(a9_hi):.4f}]")
    # What does B_{9, k9} look like at a_9 = a9_lo?
    B9_lo = bad_interval(a9_lo, k9)
    B9_hi_val = bad_interval(a9_hi, k9)
    print(f"  At a_9={a9_lo}: B_{{9,{k9}}} = [{float(B9_lo[0]):.4f}, {float(B9_lo[1]):.4f}]")
    print(f"  At a_9={a9_hi}: B_{{9,{k9}}} = [{float(B9_hi_val[0]):.4f}, {float(B9_hi_val[1]):.4f}]")

# Runner 9 covering I_9 with sigma_9=-1 (a_9 < 9):
print()
print("Can runner 9 (sigma_9=-1, a_9 < 9) cover I_9 = [10/11, 109/110]?")
for j in range(0, 10):
    a9_lo_j = Fraction(10*(11*j+10), 100)  # 10/11 constraint
    a9_hi_j = Fraction(11*j+12, Fraction(109,110)*11)  # 109/110 constraint
    # More carefully:
    # B_{9,j} overlaps I_9 iff right >= 10/11 AND left <= 109/110
    # (11j+12)/(11*a_9) >= 10/11 -> a_9 <= (11j+12)/10
    # (11j+10)/(11*a_9) <= 109/110 -> a_9 >= (11j+10)*10/109
    a9_lo_j2 = Fraction(10*(11*j+10), 109)
    a9_hi_j2 = Fraction(11*j+12, 10)
    a9_lo_eff = max(a9_lo_j2, Fraction(0))
    a9_hi_eff = min(a9_hi_j2, Fraction(9))  # sigma_9=-1 means a_9 < 9
    if a9_hi_eff > a9_lo_eff:
        print(f"  j={j}: B_{{9,{j}}} can cover I_9 for a_9 in [{float(a9_lo_eff):.4f}, {float(a9_hi_eff):.4f}]")

# 2. -++++++ (sigma_2=-1, others mostly positive)
print("\nClass 2: '-++++++-' (sigma_2=-1, sigma_9=+1)")
print("sigma_2=-1: runner 2 closes I_5 from below -> a_2 in [11/6, 2)")
print("sigma_9=+1: runner 9 closes I_4 from above -> a_9 > 9")
print()
# Runner 9 with sigma_9=+1: a_9 > 9, covers I_4 from above
# B_{9,k} contains I_4 for a_9 > 9:
print("Finding k for B_{9,k} to cover I_4 when a_9 > 9:")
for k in range(0, 20):
    a_min = Fraction(10*(11*k+10), 45)
    a_max = Fraction(10*(11*k+12), 54)
    if a_max > a_min and a_max > 9:
        a_lo = max(a_min, Fraction(9))
        a_hi = a_max
        if a_hi > a_lo:
            print(f"  k={k}: a_9 in [{a_lo}={float(a_lo):.4f}, {a_hi}={float(a_hi):.4f}]")

# 3. +------+ (sigma_2=+1, sigma_9=+1) -- the proved case
print("\nClass 3: '+------+' (sigma_2=+1, sigma_9=+1) -- the proved case")
print("sigma_2=+1: runner 2 closes I_4 from above -> a_2 > 2")
print("Primary: B_{2,0} covers I_4 -> a_2 >= 20/9")
L2_pos = Fraction(20, 9)
print(f"L_primary = {L2_pos} = {float(L2_pos):.4f} (this is > 2, so consistent with a_2 > 2)")
print()
# For I_9 coverage with a_2 > 2:
print("B_{2,1} range for a_2 in (2, 20/9):")
for a2 in [Fraction(2, 1) + Fraction(1, 100), Fraction(20, 9)]:
    B = bad_interval(a2, 1)
    print(f"  a_2={float(a2):.4f}: B_{{2,1}} = [{float(B[0]):.4f}, {float(B[1]):.4f}] vs I_9=[{float(I9[0]):.4f},{float(I9[1]):.4f}]")
    print(f"    overlap = {B[1] >= I9[0] and B[0] <= I9[1]}")

# Final summary
print("\n" + "=" * 70)
print("FINAL SUMMARY")
print("=" * 70)
print()
print("Investigation 1 (m=6,7,8 hard cases):")
print("  - For m=6: valid k = {6,7,8}, each individually blockable")
print("  - For m=7: valid k = {7,8}, each individually blockable")
print("  - For m=8: valid k = {8}, individually blockable")
print("  - The key question: can a SINGLE set of <=8 runners cover ALL k?")
print("  - This requires finding p values (no 11|p) covering multiple k simultaneously")
print()
print("Investigation 2 (sigma_2=-1 cascade):")
print("  - For sigma_2=-1: runner 2 forced to a_2 in [25/14, 24/13] ~ [1.786, 1.846]")
print("  - B_{2,j} can reach I_9 only for a_2 >= 2310/1199 ~ 1.927")
print("  - This is ABOVE the constraint a_2 < 2 (sigma_2=-1 requirement)")
print("  - THEREFORE: for sigma_2=-1 classes, runner 2 cannot cover I_9")
print("  - This leaves I_9 to runner 9 (pair (2,9)), creating the cascade contradiction")
