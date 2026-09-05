import sys
import random
from _sigma_chi2_scan_v1 import build

p = 2**256 - 2**32 - 977
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G = (Gx, Gy)

print("Building structure...")
eis, eps, beta, R1, R2, DET = build(p)

def get_eps(X):
    return eps(X)

# Binary search for block boundary between lo and hi
# (where eps changes from one value to another)
def find_boundary(lo, hi):
    lo_val = get_eps(lo)
    hi_val = get_eps(hi)
    if lo_val == hi_val:
        return None
    while hi - lo > 1:
        mid = (lo + hi) // 2
        mid_val = get_eps(mid)
        if mid_val == lo_val:
            lo = mid
        else:
            hi = mid
    return hi

print(f"R1 = {R1}")
print(f"R2 = {R2}")
print(f"DET = {DET}")
print(f"R1[1] + R2[1] = {R1[1] + R2[1]}")
print(f"DET / (R1[1]+R2[1]) = {DET // (R1[1] + R2[1])}  (predicted block spacing)")
print()

# Find 50 boundaries by scanning from random starts
boundaries = []
attempts = 0
while len(boundaries) < 50 and attempts < 500:
    attempts += 1
    x = random.randrange(1, p - 2**130)
    # scan forward to find a transition
    found = False
    for delta in [2**120, 2**125, 2**128, 2**130, 2**132]:
        x2 = x + delta
        if x2 >= p: continue
        b = find_boundary(x, x2)
        if b is not None:
            boundaries.append(b)
            found = True
            break
    if not found:
        # try scanning backward
        x2 = max(1, x - 2**130)
        b = find_boundary(x2, x)
        if b is not None:
            boundaries.append(b)

boundaries.sort()
print(f"Found {len(boundaries)} boundaries.")
print("\nBoundary positions and spacings:")
prev = None
spacings = []
for b in boundaries:
    if prev is not None:
        sp = b - prev
        spacings.append(sp)
        print(f"  boundary = {b}  spacing = {sp}")
    else:
        print(f"  boundary = {b}")
    prev = b

if spacings:
    print(f"\nSpacing statistics:")
    print(f"  count: {len(spacings)}")
    print(f"  min: {min(spacings)}")
    print(f"  max: {max(spacings)}")
    print(f"  ratio max/min: {max(spacings) / min(spacings):.6f}")
    print(f"  mean: {sum(spacings) // len(spacings)}")
    # Check if all spacings are equal
    if len(set(spacings)) == 1:
        print(f"  ALL SPACINGS IDENTICAL: {spacings[0]}")
    else:
        print(f"  distinct spacings: {len(set(spacings))}")
        print(f"  unique values: {sorted(set(spacings))[:10]}")

print("\n--- Done ---")
