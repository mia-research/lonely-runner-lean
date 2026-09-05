from fractions import Fraction

def find_blocking_pairs(m, max_p=200):
    """
    For given m, find all (p, k) where runner p wrap-blocks I_k^(m).
    Returns dict: k -> list of blocking p values.
    """
    results = {}  # k -> [p values that block it]

    # Only k values where I_k^(m) overlaps W_0 = [1/11, 10/11]
    # I_k^(m) left = (11k+1)/(121m) >= 1/11 => k >= 10/11 => k >= 1
    # I_k^(m) right = (11k+10)/(121m) <= 10/11 => 11k+10 <= 110m => k <= (110m-10)/11
    k_max = (110*m - 10) // 11
    k_max = min(k_max, 8)  # cap at 8
    k_min = 1  # but some may be below W_lo

    # Also filter: I_k^(m) must intersect [1/11, 10/11]
    valid_k = []
    for k in range(1, k_max + 1):
        ilo = Fraction(11*k + 1, 121*m)
        ihi = Fraction(11*k + 10, 121*m)
        if ihi >= Fraction(1, 11) and ilo <= Fraction(10, 11):
            valid_k.append(k)

    for k in valid_k:
        results[k] = []

    # Check all runners p=1,...,max_p not divisible by 11
    for p in range(1, max_p + 1):
        if p % 11 == 0:
            continue
        for k in valid_k:
            t_left = Fraction(11*k + 1, 121*m)
            t_right = Fraction(11*k + 10, 121*m)
            frac_left = (p * t_left) % 1
            frac_right = (p * t_right) % 1
            # Wrap-block: left in (10/11, 1) AND right in (0, 1/11)
            if frac_left > Fraction(10, 11) and frac_right < Fraction(1, 11):
                results[k].append(p)

    return valid_k, results

# Main investigation
print("WITM Fitting Step Investigation")
print("=" * 70)
print("For each m: which I_k^(m) can be blocked? Which are ALWAYS free?")
print()

for m in range(1, 13):
    valid_k, blocking = find_blocking_pairs(m)
    free_k = [k for k in valid_k if len(blocking[k]) == 0]
    blocked_k = [k for k in valid_k if len(blocking[k]) > 0]

    print(f"m={m}: valid k in W_0 = {valid_k}")
    for k in valid_k:
        if blocking[k]:
            # Show the smallest p that blocks each k and its residue
            min_p = min(blocking[k])
            print(f"  I_{k}^({m}): blocked by p = {blocking[k][:5]}... (min p={min_p}, r={min_p%11})")
        else:
            print(f"  I_{k}^({m}): PERMANENTLY FREE (no runner can block it)")
    print(f"  Summary: {len(free_k)} free interval(s): {free_k}, {len(blocked_k)} blockable: {blocked_k}")
    print()

# Now look at WHICH residues r = p mod 11 are responsible for blocking each k
print("=" * 70)
print("Pattern analysis: for each (m, k), what residue r blocks I_k^(m)?")
print()
print(f"{'m':<4}", end="")
for k in range(1, 9):
    print(f"  I_{k}^(m)", end="")
print()
print("-" * 80)

for m in range(1, 13):
    valid_k, blocking = find_blocking_pairs(m)
    print(f"{m:<4}", end="")
    for k in range(1, 9):
        if k not in valid_k:
            print(f"  [----]", end="")
        elif not blocking[k]:
            print(f"  [FREE]", end="")
        else:
            r = min(blocking[k]) % 11
            print(f"  r={r:2d}  ", end="")
    print()

print()
print("=" * 70)
print("KEY INSIGHT SEARCH:")
print("Is there always at least one permanently free interval k in {1,...,8} ∩ W_0?")
print()
for m in range(1, 25):
    valid_k, blocking = find_blocking_pairs(m)
    free_k = [k for k in valid_k if len(blocking[k]) == 0]
    blockable_k = [k for k in valid_k if len(blocking[k]) > 0]
    can_all_be_blocked = (len(free_k) == 0)
    print(f"m={m:2d}: valid_k={valid_k}, free={free_k}, blockable={blockable_k}, "
          f"all_blockable={can_all_be_blocked}")

print()
print("=" * 70)
print("PROOF SKETCH:")
print("For each m, identify the algebraic reason why some k is free.")
print()

# Derive the condition: for wrap-blocking I_k^(m) by runner p=r (q=0, r<22m/9):
# {r*(11k+1)/(121m)} > 10/11 AND {r*(11k+10)/(121m)} < 1/11
# This requires r*(11k+1) in (110m*n+110m-11, 110m*n+110m) [some n]
# AND r*(11k+10) in (110m*n+110m, 110m*n+110m+11) [same n]
# BOTH: r*(2k+1) must be close to 2n*110m/11 + (specific residue)
# The key: r*(2k+1) must ≡ 0 mod 11 ... let's check

print("Modular structure of blocking condition:")
print("When runner r wrap-blocks I_k^(m), what is r*(2k+1) mod 11?")
print()
for m in range(1, 7):
    valid_k, blocking = find_blocking_pairs(m)
    print(f"m={m}:")
    for k in valid_k:
        for p in blocking[k][:3]:  # first 3 blockers
            r = p % 11
            val = r * (2*k + 1)
            print(f"  k={k}, p={p} (r={r}): r*(2k+1) = {val} ≡ {val % 11} (mod 11)")
    print()
