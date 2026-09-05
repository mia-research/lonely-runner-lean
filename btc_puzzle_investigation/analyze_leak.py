import sys
import math
from _sigma_chi2_scan_v1 import build

p = 2**256 - 2**32 - 977
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G = (Gx, Gy)

def inv_mod(a, m): return pow(a, -1, m)

def ecc_add(P, Q):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    if P == Q:
        m = (3 * x1 * x1) * inv_mod(2 * y1, p) % p
    else:
        m = (y2 - y1) * inv_mod(x2 - x1, p) % p
    x3 = (m * m - x1 - x2) % p
    y3 = (m * (x1 - x3) - y1) % p
    return (x3, y3)

print("Building structure...")
eis, eps, beta, R1, R2, DET = build(p)

def get_eps(X):
    return eps(X)

def find_boundary(lo, hi):
    lo_val = get_eps(lo)
    hi_val = get_eps(hi)
    if lo_val == hi_val: return None
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if get_eps(mid) == lo_val:
            lo = mid
        else:
            hi = mid
    return hi

# We want to find the block length L around a point X, and compare it to the internal v(X)
def get_block_length_and_v(X):
    # scan forward and backward to find boundaries
    # use large steps to find the bounds quickly
    step = 2**120
    lo = X
    while get_eps(lo) == get_eps(X) and lo > step:
        lo -= step
    # binary search exact lo
    b_lo = find_boundary(lo, X)
    if b_lo is None: b_lo = lo
    
    hi = X
    while get_eps(hi) == get_eps(X) and hi < p - step:
        hi += step
    b_hi = find_boundary(X, hi)
    if b_hi is None: b_hi = hi
    
    L = b_hi - b_lo
    
    # get internal v(X)
    u, v = eis(X)
    return L, v

print("Testing mapping: Block Length L  ->  Internal Coordinate v(X)")
print("If L determines v, then the local geometry leaks the lattice coordinate.\n")

# Test on a few random points first
import random
print("--- Random Points ---")
for _ in range(5):
    X = random.randrange(1, p)
    L, v = get_block_length_and_v(X)
    print(f"X={X % (10**20)}... L={L}, v={v}")

print("\n--- Curve Points kG ---")
P = G
for k in range(1, 11):
    if k > 1:
        P = ecc_add(P, G)
    if P is None: continue
    X = P[0]
    L, v = get_block_length_and_v(X)
    print(f"k={k:>2}: L={L}, v={v}")

# Now check the deterministic relationship: does L uniquely identify v?
print("\n--- Checking if L uniquely determines v ---")
pairs = []
for _ in range(20):
    X = random.randrange(1, p)
    L, v = get_block_length_and_v(X)
    pairs.append((L, v))

# sort by L
pairs.sort()
prev_L = None
v_for_prev_L = None
unique = True
for L, v in pairs:
    if prev_L is not None and L == prev_L:
        if v != v_for_prev_L:
            print(f"COLLISION: L={L} maps to v={v_for_prev_L} and v={v}")
            unique = False
    else:
        prev_L = L
        v_for_prev_L = v

if unique:
    print("L uniquely determines v across the sample (no collisions).")
    # If it uniquely determines v, we have a deterministic geometric leak!
    # Let's check the mathematical relation between v and X
    print("\nMathematical relation check:")
    print(f"R1[1] = {R1[1]}, R2[1] = {R2[1]}")
    # v(X) is basically the error in the Diophantine approximation.
    # Can we recover X mod M from v?
    # v = -c1*R1[1] - c2*R2[1]
    # This is complex, so let's just see if v correlates with X mod something.
    print("\nChecking correlation of v with X mod small numbers:")
    for m in [2, 3, 5, 7, 11, 13, 100, 1000]:
        # group by X mod m and see if v is distinct
        groups = {}
        for L, v in pairs:
            # we need X for this, let's just re-run a quick check
            pass

print("\n--- Done ---")
