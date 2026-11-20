# v3_passtype_census_v1 -- E883 generalized: the reach-passing type census for the (rho_4,1)-anchored family.
# Type = (hinge reading y, hinge lap k, cover lap j >= k): the tight-tree solution u_y = 33/((8k-1)*7)
# (hinge row u_y <= (33/(8k-1)) u_4 with the front row u_4 -> 1/7), the 7-cover by zone (y,j):
#   (8j-1) u_y < 7 < (8j+1) u_y.
# Survivor iff some integer j >= k satisfies BOTH cover rows at the tree solution AND the type's other
# fixed rows hold at the tree solution (sorted, region: u_5(idx5) < 1/17, u_6(idx6) <= 1/25, u_i <= 1).
# y = 3 excluded (self-hinge: the row u_3 <= c u_3 binds nothing).
# For each survivor: the exact u_y window (7/(8j+1), min(33/((8k-1)*7), 7/(8j-1))) and the value
# (8j+1)*33/((8k-1)*7) = the reach the type would realize. Exact Fractions throughout.
from fractions import Fraction as F

def rn(y): return f"rho{y+1}" if y > 0 else "rho1"

# region caps: u_5 < 1/17 (rho_6 > 17, strict), u_6 <= 1/25 (rho_7 >= 25, non-strict)
REG = {5: (F(1,17), True), 6: (F(1,25), False)}

def type_row_check(y, u):
    # sorted: u_i <= u_{i-1} for i>=2 (index order); tree value must respect sortedness vs u_3 = 1/7 (idx3)
    # and the region rows and u <= 1.
    # sorted chain: u_1 >= u_2 >= ... >= u_6; the front pins u_3* = 1/7 (idx3). For y >= 3: u_y* <= 1/7.
    # For y < 3: u_y* >= u_3* -- but the tree value is an UPPER bound construction; the sorted rows
    # constrain the OTHER readings, which are free -- a type survives the minimal system iff there is
    # an assignment; here we only check the tree value against rows that bind u_y itself:
    if y >= 3 and u > F(1,7): return False            # u_y <= u_3 (sorted, at the front extreme)
    if y in (1, 2) and u < F(1,7): return False       # u_1, u_2 >= u_3 = 1/7 (sorted, at the front extreme)
    if y in (1, 2) and u > F(1): return False         # rho_2, rho_3 >= 1
    if y in REG:
        cap, strict = REG[y]
        if strict and u >= cap: return False
        if not strict and u > cap: return False
    return True

print("== (rho_4,1)-anchored reach-passing type census (tree solution u_y = 33/((8k-1)*7)) ==")
survivors = []
for y in [1, 2, 4, 5, 6]:
    kmax = 80
    for k in range(1, kmax + 1):
        u_tree = F(33, (8*k - 1) * 7)
        if not type_row_check(y, u_tree):
            continue
        # cover laps j >= k with (8j-1)u < 7 < (8j+1)u at u = u_tree:
        #   8j+1 > 49(8k-1)/33  and  8j-1 < 49(8k-1)/33
        C = F(49 * (8*k - 1), 33)
        jlo = max(k, -(-(C - 1 - 1) // 8))  # 8j > C - 2  => j > (C-2)/8
        for j in range(jlo, jlo + 4):
            if 8*j - 1 < C and 8*j + 1 > C:
                ulo = F(7, 8*j + 1)
                uhi = min(u_tree, F(7, 8*j - 1))
                if ulo < uhi:
                    val = F(8*j + 1) * u_tree
                    survivors.append((y, k, j, ulo, uhi, val))
if survivors:
    print(f"{'y':>2} {'k':>3} {'j':>3}  u-window                                value")
    for (y, k, j, ulo, uhi, val) in survivors:
        print(f"{y:>2} {k:>3} {j:>3}  ({ulo}, {uhi})  {val}")
    print(f"\n{len(survivors)} survivor types in the k <= 80 census")
    vals = sorted(set(v for (*_, v) in survivors))
    print("distinct values:", [str(v) for v in vals[:12]])
    print("max value:", max(vals), " (7 = 5831/833; value > 7 would be a carve)")
else:
    print("no survivor types found in range")
