"""Manually verify the smallest LRC-like counterexample:
n=3, G_speeds=[3], A_speeds=[1,5], p=2.
Cross-check that all hypotheses match Lean's joint_fine_cell_exists exactly."""

import math

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

def lcm(a, b):
    return a * b // math.gcd(a, b)
def lcm_list(xs):
    L = 1
    for x in xs:
        L = lcm(L, x)
    return L


n = 3
G_speeds = [3]
A_speeds = [1, 5]
p = 2
L_G = lcm_list(G_speeds)
L_A = lcm_list(A_speeds)
M_A = n * L_G * L_A

print(f"n={n}, G_speeds={G_speeds}, A_speeds={A_speeds}, p={p}")
print(f"L_G={L_G}, L_A={L_A}, M_A={M_A}, n*L_G={n*L_G}, n*L_G*L_A*p={n*L_G*L_A*p}")
print()

# Hypothesis checks
print("Hypotheses (mirror Lean):")
print(f"  3 ≤ n:            {3 <= n}")
print(f"  L_G > 0:          {L_G > 0}")
print(f"  L_A > 0:          {L_A > 0}")
print(f"  1 < p:            {1 < p}")
print(f"  gcd(p, L_G) = 1:  {math.gcd(p, L_G) == 1}")
print(f"  all G_speeds > 0: {all(v > 0 for v in G_speeds)}")
print(f"  all A_speeds > 0: {all(v > 0 for v in A_speeds)}")
G_idx = good_cell_idx(G_speeds, n, L_G)
A_idx = good_cell_idx(A_speeds, n, L_A)
print(f"  goodCellIdx_G:    {G_idx}  (nonempty: {len(G_idx) > 0})")
print(f"  goodCellIdx_A:    {A_idx}  (nonempty: {len(A_idx) > 0})")
print(f"  HARD CASE p<n·L_G: {p < n * L_G}  (n·L_G = {n*L_G})")
print()

# Exhaustive search
print(f"Searching m'' < {n*L_G*L_A*p}:")
found = False
joint_count = 0
for mpp in range(n * L_G * L_A * p):
    alpha = mpp // (L_A * p)
    beta = (mpp % M_A) // L_G
    if alpha in G_idx and beta in A_idx:
        joint_count += 1
        if not found:
            print(f"  FIRST WITNESS: m''={mpp}, α={alpha}, β={beta}")
        found = True

print(f"\nJoint count: {joint_count}")
if joint_count == 0:
    print(">>> CONFIRMED COUNTEREXAMPLE: joint_fine_cell_exists is FALSE here.")
else:
    print(">>> No counterexample (joint count > 0).")
