import sys
import random
from _sigma_chi2_scan_v1 import build

p = 2**256 - 2**32 - 977
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G = (Gx, Gy)

print("Building structure...")
eis, eps, beta, R1, R2, DET = build(p)

# The hypothesized 1D slope
M = (R2[1] - R1[1]) % p
print(f"M = {M}")

def get_eps(X):
    return eps(X)

def cen(y, p):
    y %= p
    return y - p if y > p // 2 else y

# Hypothesis: eps(X) != 0  <=>  cen(M * X % p) in (p/4, p/2) or (-p/2, -p/4)
def predict_eps(X):
    Y = cen((M * X) % p, p)
    if Y > p // 4 or Y < -(p // 4):
        return 1 # non-zero
    return 0

print("\nTesting exact 1D reduction: eps(X) == sgn(c(M*X))...")
mismatches = 0
N = 10000
for _ in range(N):
    X = random.randrange(1, p)
    actual = 1 if get_eps(X) != 0 else 0
    pred = predict_eps(X)
    if actual != pred:
        mismatches += 1

print(f"Tested {N} random points.")
print(f"Mismatches: {mismatches}")
if mismatches == 0:
    print("EXACT MATCH. The 2D structure is strictly a 1D sawtooth wave c(M*X).")
else:
    print("Hypothesis failed. The structure is genuinely 2D.")

print("\n--- Done ---")
