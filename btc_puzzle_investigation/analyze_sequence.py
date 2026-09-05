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

N = 200
seq = []
P = G
for k in range(1, N + 1):
    if k > 1:
        P = ecc_add(P, G)
    if P is None:
        seq.append(0)
        continue
    seq.append(1 if get_eps(P[0]) != 0 else 0)

print(f"\n--- Rigorous Statistical Map of Sequence (N={N}) ---")

# 1. Density
ones = sum(seq)
print(f"Total 1s: {ones} / {N} (Density: {ones/N:.3f}, Expected ~0.250)")

# 2. Transitions
t00 = sum(1 for i in range(N-1) if seq[i]==0 and seq[i+1]==0)
t01 = sum(1 for i in range(N-1) if seq[i]==0 and seq[i+1]==1)
t10 = sum(1 for i in range(N-1) if seq[i]==1 and seq[i+1]==0)
t11 = sum(1 for i in range(N-1) if seq[i]==1 and seq[i+1]==1)
print(f"Transitions: 00={t00}, 01={t01}, 10={t10}, 11={t11}")
print(f"  (Expected 11 rate: ~0.062)")

# 3. Longest run of 0s
max_run = 0
cur_run = 0
for s in seq:
    if s == 0:
        cur_run += 1
        max_run = max(max_run, cur_run)
    else:
        cur_run = 0
print(f"Longest run of 0s: {max_run} (Expected ~18-20)")

# 4. Density by k mod m
print("Density by k mod m (looking for structural periodicity):")
for m in [2, 3, 4, 5, 6, 7]:
    counts = [0]*m
    totals = [0]*m
    for k in range(1, N+1):
        totals[k%m] += 1
        if seq[k-1] == 1:
            counts[k%m] += 1
    densities = ", ".join(f"{counts[i]}/{totals[i]}" for i in range(m))
    print(f"  mod {m}: {densities}")

# 5. Autocorrelation
def autocorrel(seq, lag):
    matches = sum(1 for i in range(len(seq)-lag) if seq[i]==seq[i+lag])
    return matches / (len(seq)-lag)
print("Autocorrelation (probability of matching at lag):")
print("  (Expected ~0.625 for pure noise. 1.0 = perfect period)")
for lag in range(1, 13):
    print(f"  lag={lag:>2}: {autocorrel(seq, lag):.3f}")

print("\n--- Done ---")
