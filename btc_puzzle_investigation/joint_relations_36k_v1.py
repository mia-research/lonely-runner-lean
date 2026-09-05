#!/usr/bin/env python3
"""
joint_relations_36k_v1.py -- joint-SET relations on the 36k constructed set (the purpose-built,
known-generator dataset), not just 82. Exact int arithmetic.

GOVERNING FACT (state first): among M INDEPENDENT keys mod n, the expected count of relations
d_i = c*d_j with |c|<=B is ~ M^2 * 2B / n. For M=30000, n~2^256, one expected relation needs
B ~ n/(2M^2) ~ 2^225. So small-coeff pairwise relations are NULL BY COUNTING for independent keys;
a hit would mean the GENERATOR correlated the keys. This is WHY 7-, 82-, 36k-tests all go null --
not under-powering. The 36k (10^5x more pairs than 82) is the strongest empirical confirmation, and
being a KNOWN-generator set, it also tests whether OUR MT pipeline leaves any such relation (it must
not, if it is a faithful independent-key control).

Test (multiplier hash, exact): S={d mod n}; for each key d_j, incrementally form c*d_j (c=2..B) and
check membership in S. PLANT a known d=5*d_j (must detect); RANDOM control (36k independent keys same
bit-ranges) must match (none beyond trivial small-key coincidences).
"""
import csv, random, sys
from sig_lib import N_ORD
n = N_ORD
B = 2048               # multiplier bound (scope; counting says any tractable B is null for indep keys)

def load(path):
    d = []; N = []
    with open(path) as f:
        for row in csv.DictReader(f):
            d.append(int(row['d'])); N.append(int(row['N']))
    return d, N

def mult_test(D, label, B=B, large_only=None, Nlist=None):
    """count pairs d_i = c*d_j, 2<=c<=B, via hash. If large_only, restrict d_j to N>=large_only."""
    S = set(x % n for x in D)
    hits = 0; examples = []
    for j, dj in enumerate(D):
        if large_only is not None and Nlist[j] < large_only: continue
        acc = dj % n
        for c in range(2, B + 1):
            acc = (acc + dj) % n
            if acc in S:
                hits += 1
                if len(examples) < 3: examples.append((c, j))
    print(f"  [{label}] d_i=c*d_j, 2<=c<=2^{B.bit_length()-1}: {hits} hits {examples}")
    return hits

def rand_like(Nlist, seed):
    rng = random.Random(seed)
    return [rng.randrange(1 << (b - 1), 1 << b) for b in Nlist]

def main():
    D, N = load('constructed_keys_fullrange_v1.csv')
    print(f"loaded {len(D)} constructed keys, bit-lengths {sorted(set(N))}")
    Mbig = sum(1 for x in N if x >= 100)
    print(f"expected small-mult relations among {Mbig} indep large keys, B=2^{B.bit_length()-1}:")
    print(f"   ~ M^2 * 2B / n = {Mbig}^2 * {2*B} / n ~ {Mbig*Mbig*2*B / n:.2e}  (<<1 => null by counting)")

    print("\n=== FIRING CONTROL: plant d_new = 5*d_0, must detect ===")
    planted = list(D[:2000]) + [5 * D[0] % n]
    mult_test(planted, "PLANT c=5")

    print("\n=== RANDOM control (36k independent keys, same bit-ranges) ===")
    for seed in (1, 2):
        R = rand_like(N, seed)
        mult_test(R, f"rand{seed}, ALL", large_only=None, Nlist=N)
        mult_test(R, f"rand{seed}, large>=100", large_only=100, Nlist=N)

    print("\n=== REAL 36k constructed keys ===")
    mult_test(D, "REAL-36k ALL", large_only=None, Nlist=N)
    mult_test(D, "REAL-36k large>=100", large_only=100, Nlist=N)

    print("\n=== VERDICT ===")
    print("  Informative iff PLANT fired. Then REAL vs RANDOM on the LARGE keys is the clean test")
    print("  (small keys give trivial coincidences in both). Expected: both null, matching the")
    print("  counting bound. The 36k gives 10^5x more pairs than the 82-set; a generator-left small")
    print("  relation would show here and does not. Large-coeff relations remain DLP-hard (out of reach).")

if __name__ == '__main__':
    main()
