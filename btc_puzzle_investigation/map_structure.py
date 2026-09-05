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

eis, eps, beta, R1, R2, DET = build(p)

def sig(X, cand):
    a, b = eis(X)
    u_num = a * R2[1] - b * R2[0]
    v_num = b * R1[0] - a * R1[1]
    num = u_num - v_num if cand == '-' else u_num + v_num
    if 2 * abs(num) > abs(DET):
        return 1 if num > 0 else -1
    return 0

cand = '-'
for _ in range(100):
    X = random.randrange(1, p)
    if eps(X) == 0: continue
    if sig(X, '-') != 0: cand = '-'; break
    if sig(X, '+') != 0: cand = '+'; break

def analyze_window(x_center, delta):
    vals = []
    start = (x_center - delta) % p
    for i in range(2 * delta + 1):
        X = (start + i) % p
        if X == 0:
            vals.append(0)
            continue
        s_val = sig(X, cand)
        if s_val != 0:
            c2 = 1 if pow(X, (p-1)//2, p) == 1 else -1
            vals.append(s_val * c2)
        else:
            vals.append(0)
    return vals

delta = 2000
print(f"Mapping random window (conservation law) with delta={delta}...")
x_rand = random.randrange(1, p)
v_rand = analyze_window(x_rand, delta)
print(f"Sum: {sum(v_rand)}, Non-zeros: {sum(1 for v in v_rand if v != 0)}")
print(f"First 50 values: {v_rand[:50]}")

print(f"\nMapping k=5 window (anomaly) with delta={delta}...")
P = scalar_mult(5)
if P is not None:
    v_k5 = analyze_window(P[0], delta)
    print(f"Sum: {sum(v_k5)}, Non-zeros: {sum(1 for v in v_k5 if v != 0)}")
    nz_indices = [i for i, v in enumerate(v_k5) if v != 0]
    if nz_indices:
        print(f"First 20 non-zero indices: {nz_indices[:20]}")
        print(f"Values at those indices: {[v_k5[i] for i in nz_indices[:20]]}")
    else:
        print("No non-zero values found in k=5 window.")
