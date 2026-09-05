import sys
import random
from _sigma_chi2_scan_v1 import build, sigma_fn

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
try:
    eis, eps, beta, R1, R2, DET = build(p)
    sig, ori = sigma_fn(p, eis, eps, R1, R2, DET)
    print(f"Structure built. Orientation: {ori}")
except Exception as ex:
    print(f"Build failed at 256-bit: {ex}")
    sys.exit(0)

def local_sum(x_center, delta):
    s = 0
    start = (x_center - delta) % p
    for i in range(2 * delta + 1):
        X = (start + i) % p
        if X == 0: continue
        try:
            s_val = sig(X)
        except:
            s_val = sig[X] if X < len(sig) else 0
            
        if s_val != 0:
            c2 = 1 if pow(X, (p-1)//2, p) == 1 else -1
            s += s_val * c2
    return s

delta = 5000
print(f"\nSampling baseline (random x) with delta={delta}...")
for _ in range(5):
    x = random.randrange(1, p)
    val = local_sum(x, delta)
    print(f"  Random x sum: {val}")

print(f"\nSampling curve points kG with delta={delta}...")
for k in [2, 3, 5, 7, 11, 13, 17, 19]:
    P = scalar_mult(k)
    if P is None: continue
    x_kG = P[0]
    val = local_sum(x_kG, delta)
    print(f"  k={k} sum: {val}")

print("\n--- Done ---")
