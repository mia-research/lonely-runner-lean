import sys
import random
import time
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

print(f"Building structure for secp256k1 (p % 24 = {p % 24})...")
t = time.time()
eis, eps, beta, R1, R2, DET = build(p)
print(f"Structure built in {time.time()-t:.2f}s. DET={DET}")

# We must use the EXACT eps function from the original code to get the true sigma
def sig_exact(X):
    # eps returns 0, 1, or 2. 
    # The original code maps this to 0, +1, -1 based on orientation.
    # We just need to know if it's non-zero (flap) to multiply by chi2.
    # Since FLD = sum sigma * chi2, and sigma is 0 or +/-1, 
    # we can just use eps(X) != 0 to find the flap points.
    # However, the SIGN matters for the sum.
    # Let's use the exact reduction from the original code to get the sign.
    from fractions import Fraction as Fr
    def co(w):
        a, b = w
        return Fr(a * R2[1] - b * R2[0], DET), Fr(b * R1[0] - a * R1[1], DET)
    
    u, v = co(eis(X))
    # Try both orientations safely
    s_minus = u - v
    s_plus = u + v
    
    # The original code's pre-flight check ensures one of these matches eps(X)
    # We can determine the sign by checking which one falls outside (-1/2, 1/2)
    if abs(s_minus) > Fr(1, 2):
        return 1 if s_minus > 0 else -1
    elif abs(s_plus) > Fr(1, 2):
        return 1 if s_plus > 0 else -1
    return 0

def local_sum(x_center, delta):
    s = 0
    count_nonzero = 0
    start = (x_center - delta) % p
    for i in range(2 * delta + 1):
        X = (start + i) % p
        if X == 0: continue
        s_val = sig_exact(X)
        if s_val != 0:
            c2 = 1 if pow(X, (p-1)//2, p) == 1 else -1
            s += s_val * c2
            count_nonzero += 1
    return s, count_nonzero

delta = 2000
print(f"\nSampling baseline (random x) with delta={delta}...")
for _ in range(3):
    x = random.randrange(1, p)
    s, c = local_sum(x, delta)
    print(f"  Random x: sum={s}, nonzero={c}")

print(f"\nSampling curve points kG with delta={delta}...")
for k in [2, 3, 5, 7, 11, 13, 17, 19]:
    P = scalar_mult(k)
    if P is None: continue
    s, c = local_sum(P[0], delta)
    print(f"  k={k}: sum={s}, nonzero={c}")

print("\n--- Done ---")
