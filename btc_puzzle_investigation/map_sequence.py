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

# We use the exact eps() to get the flap state (0, 1, or 2)
def get_eps(X):
    return eps(X)

print("Mapping sequence of eps(x_k) for k = 1 to 200...")
print("Looking for patterns outside the C_3 symmetry (e.g., dependence on k mod 3)\n")

P = None
# Print header
print("k  | k%3 | eps(x_k) | sequence")
print("-" * 40)

seq = []
for k in range(1, 201):
    if k == 1:
        P = G
    else:
        P = ecc_add(P, G)
    
    if P is None:
        print(f"{k:<3}| {k%3:<3} | NULL     |")
        seq.append('N')
        continue
    
    x = P[0]
    s = get_eps(x)
    seq.append(str(s))
    
    # Print in blocks to see patterns
    if k % 30 == 0:
        print(f"{k:<3}| {k%3:<3} | {s:<8} | {''.join(seq[-30:])}")

print("\n--- Full Sequence ---")
# Print the full sequence grouped by 10s
for i in range(0, len(seq), 30):
    print(f"k={i+1:>3}: {' '.join(seq[i:i+30])}")

print("\n--- Done ---")
