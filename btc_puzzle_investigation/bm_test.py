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

print("Building structure...")
eis, eps, beta, R1, R2, DET = build(p)

def get_sigma(X):
    return 1 if eps(X) != 0 else 0

N = 512
print(f"Generating {N} curve points and extracting binary sigma(x_k)...")
seq = []
P = G
for k in range(N):
    if k > 0:
        P = ecc_add(P, G)
    if P is None:
        seq.append(0)
    else:
        seq.append(get_sigma(P[0]))

# Berlekamp-Massey over GF(2)
def gf2_bm(s):
    n = len(s)
    c = [0]*n; b = [0]*n
    c[0] = 1; b[0] = 1
    L = 0; m = 1
    for i in range(n):
        d = s[i]
        for j in range(1, L+1):
            d ^= c[j] & s[i-j]
        if d == 0:
            m += 1
        elif 2 * L <= i:
            t = c[:]
            for j in range(n - m):
                c[j+m] ^= b[j]
            L = i + 1 - L
            b = t
            m = 1
        else:
            for j in range(n - m):
                c[j+m] ^= b[j]
            m += 1
    return L

print("\n--- Berlekamp-Massey Linear Complexity ---")
lc_curve = gf2_bm(seq)
print(f"Linear complexity of curve sequence: {lc_curve}")
print(f"(For a random sequence of length {N}, expected complexity is ~{N//2})")

# Compare to random
random_seq = [random.randint(0, 1) for _ in range(N)]
lc_random = gf2_bm(random_seq)
print(f"Linear complexity of random sequence: {lc_random}")

if lc_curve < N // 4:
    print("\nANOMALY: Linear complexity is significantly lower than expected.")
    print("The sequence of flap states contains a linear structure (LFSR).")
elif lc_curve >= N // 2 - 5 and lc_curve <= N // 2 + 5:
    print("\nNULL: Linear complexity is exactly N/2, consistent with pure randomness.")
else:
    print(f"\nUNEXPECTED: Linear complexity is {lc_curve}. Neither a clear leak nor a clear null.")

print("\n--- Done ---")
