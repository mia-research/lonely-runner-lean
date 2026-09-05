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

def get_eps(X):
    return eps(X)

N = 10000
print(f"Generating {N} curve points and mapping eps(x_k)...")
seq = []
P = G
for k in range(1, N + 1):
    if k > 1:
        P = ecc_add(P, G)
    if P is None:
        seq.append(0)
        continue
    seq.append(1 if get_eps(P[0]) != 0 else 0)
    if k % 1000 == 0:
        print(f"  ...{k}/{N}")

print(f"\n--- Rigorous Statistical Map of Sequence (N={N}) ---")

# 1. Density
ones = sum(seq)
exp_d = 0.25
obs_d = ones / N
z_d = (obs_d - exp_d) / (exp_d * (1 - exp_d) / N)**0.5
print(f"Total 1s: {ones} / {N} (Density: {obs_d:.4f}, Expected {exp_d:.4f}, Z-score: {z_d:.2f})")

# 2. Autocorrelation
def autocorrel(seq, lag):
    matches = sum(1 for i in range(len(seq)-lag) if seq[i]==seq[i+lag])
    return matches / (len(seq)-lag)

exp_ac = 0.625
std_ac = (exp_ac * (1 - exp_ac) / N)**0.5
print("Autocorrelation (expected ~0.625, Z-scores in brackets):")
for lag in range(1, 13):
    ac = autocorrel(seq, lag)
    z = (ac - exp_ac) / std_ac
    print(f"  lag={lag:>2}: {ac:.4f} (Z: {z:>6.2f})")

# 3. Density by k mod m
print("Density by k mod m (looking for Z-scores > 3 or < -3):")
for m in [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]:
    counts = [0]*m
    totals = [0]*m
    for k in range(1, N+1):
        totals[k%m] += 1
        if seq[k-1] == 1:
            counts[k%m] += 1
    
    max_z = 0
    max_i = -1
    for i in range(m):
        exp = totals[i] * exp_d
        std = (totals[i] * exp_d * (1 - exp_d))**0.5
        if std == 0: continue
        z = (counts[i] - exp) / std
        if abs(z) > abs(max_z):
            max_z = z
            max_i = i
    print(f"  mod {m:>2}: max Z = {max_z:>6.2f} at class {max_i}")

print("\n--- Done ---")
