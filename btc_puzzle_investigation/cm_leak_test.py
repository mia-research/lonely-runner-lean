import sys
import random
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

def scalar_mult(k):
    N = G; result = None
    while k > 0:
        if k % 2 == 1: result = ecc_add(result, N)
        N = ecc_add(N, N)
        k //= 2
    return result

print("Building structure...")
eis, eps, beta, R1, R2, DET = build(p)
b2 = (beta * beta) % p

# We use the EXACT eps(X) function to get the true flap state (0, 1, or 2)
def get_eps(X):
    return eps(X)

print(f"beta = {beta}")
print(f"Checking if sigma(x) is invariant under 120-degree rotation (x -> beta*x)...\n")

# 1. Test on random points
invariant_count = 0
nonzero_count = 0
total_tested = 10000
for _ in range(total_tested):
    x = random.randrange(1, p)
    s1 = get_eps(x)
    s2 = get_eps((beta * x) % p)
    s3 = get_eps((b2 * x) % p)
    
    if s1 != 0:
        nonzero_count += 1
        if s1 == s2 == s3:
            invariant_count += 1

print(f"Random points tested: {total_tested}")
print(f"Points with sigma(x) != 0: {nonzero_count}")
print(f"Of those, how many had identical sigma across the CM orbit: {invariant_count}")
if nonzero_count > 0:
    print(f"Invariance rate: {invariant_count / nonzero_count:.4f}")

# 2. Test on kG points
print("\nTesting kG points (x, beta*x, beta^2*x):")
for k in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]:
    P = scalar_mult(k)
    if P is None: continue
    x = P[0]
    s1 = get_eps(x)
    s2 = get_eps((beta * x) % p)
    s3 = get_eps((b2 * x) % p)
    print(f"  k={k:>2}: eps(x)={s1}, eps(beta*x)={s2}, eps(beta^2*x)={s3}  -> {'INVARIANT' if s1==s2==s3 else 'DIFFERS'}")

print("\n--- Done ---")
