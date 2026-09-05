import sys
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

print("Mapping 2D lattice coordinates (a, b) for curve points kG...")
print("Looking for a linear recurrence in the lattice coordinates.\n")

P = G
prev_a, prev_b = 0, 0
diffs_a = []
diffs_b = []

for k in range(1, 21):
    if k > 1:
        P = ecc_add(P, G)
    if P is None: break
    
    x = P[0]
    a, b = eis(x)
    
    print(f"k={k:>2}: a={a}, b={b}")
    
    if k > 1:
        diffs_a.append(a - prev_a)
        diffs_b.append(b - prev_b)
        
    prev_a, prev_b = a, b

print("\n--- Differences between consecutive lattice points ---")
print("da (delta a):")
for i, d in enumerate(diffs_a):
    print(f"  k={i+1}->k={i+2}: {d}")

print("\ndb (delta b):")
for i, d in enumerate(diffs_b):
    print(f"  k={i+1}->k={i+2}: {d}")

# Check if the differences are constant (which would mean a linear recurrence)
if len(diffs_a) > 2:
    if diffs_a[0] == diffs_a[1] == diffs_a[2]:
        print("\nCONSTANT DELTA A! Linear recurrence found in a.")
    else:
        print("\nDelta A is not constant.")
        
    # Check if second differences are constant (quadratic recurrence)
    second_diffs_a = [diffs_a[i+1] - diffs_a[i] for i in range(len(diffs_a)-1)]
    if len(set(second_diffs_a)) == 1:
        print(f"CONSTANT SECOND DELTA A! Quadratic recurrence found. d2a = {second_diffs_a[0]}")

print("\n--- Done ---")
