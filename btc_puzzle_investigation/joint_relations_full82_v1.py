#!/usr/bin/env python3
"""
joint_relations_full82_v1.py -- joint-SET relations on the FULL key set, not just the 7 exposed.

Fixes the under-powering of pubkey_relations(_controlled): those checked pairwise relations among
only 7 points. Here: ALL 82 solved keys (d known => check EXHAUSTIVELY over all multipliers, not
just c<=4096) + the 7 unsolved (via points). Curve-side relations (P_i=c*P_j, P_i=a*P_j+b*G) are
d_i = c*d_j and d_i = a*d_j + b (mod n) for the solved -- verified directly with d, full power.

Controls: PLANT a known relation (must detect); RANDOM matched key set (82 independent keys, same
bit-ranges) -> must show the same (none). Exact integer / modular arithmetic only.
"""
import csv, random
from sig_lib import P as FP, G, add, mul, N_ORD
import pickle
from nonce_lattice import decompress
n = N_ORD

# ---- load ALL 82 solved (d known) ----
solved = []
with open('puzzles_verified.csv') as f:
    for row in csv.DictReader(f):
        solved.append((int(row['puzzle']), int(row['private_key'], 16)))
solved.sort()
D = [d for _, d in solved]
BITS = [b for b, _ in solved]
print(f"solved keys: {len(D)} (puzzles {BITS[0]}..{BITS[-1]})")

recs = pickle.load(open('sweep2019_recs.pkl', 'rb'))
unsolved_pts = [(r['idx'], decompress(r['pub'])) for r in recs if 'd' not in r]
print(f"unsolved exposed points: {len(unsolved_pts)}")

def minpm(c):                       # min(|c|, n-|c|): smallness of a multiplier mod n
    c %= n
    return min(c, n - c)

# ---- Test M: pairwise multiplier d_i = c*d_j mod n, EXHAUSTIVE over c (report smallest) ----
def test_multiplier(Dlist, label, thresh=1 << 24):
    hits = []
    for i in range(len(Dlist)):
        for j in range(len(Dlist)):
            if i == j: continue
            c = Dlist[i] * pow(Dlist[j], n - 2, n) % n
            m = minpm(c)
            if m <= thresh:
                hits.append((i, j, c if c < n - c else c - n))
    print(f"  [MULT {label}] pairwise d_i=c*d_j with |c|<=2^24: {len(hits)} hits {hits[:3]}")
    return hits

# ---- Test A: affine d_i = a*d_j + b (mod n), small a, small |b| ----
def test_affine(Dlist, label, AMAX=64, BMAX=1 << 20):
    hits = []
    for i in range(len(Dlist)):
        for j in range(len(Dlist)):
            if i == j: continue
            for a in range(1, AMAX + 1):
                b = (Dlist[i] - a * Dlist[j]) % n
                if minpm(b) <= BMAX:
                    hits.append((i, j, a, b if b < n - b else b - n))
                    break
    print(f"  [AFF  {label}] d_i=a*d_j+b, a<=2^6,|b|<=2^20: {len(hits)} hits {hits[:3]}")
    return hits

# ---- Test G: pairwise gcd structure (do any two share a large factor) ----
from math import gcd
def test_gcd(Dlist, label):
    mx = 0; arg = None
    for i in range(len(Dlist)):
        for j in range(i + 1, len(Dlist)):
            g = gcd(Dlist[i], Dlist[j])
            if g > mx: mx = g; arg = (i, j)
    print(f"  [GCD  {label}] max pairwise gcd = {mx} (pair {arg})")
    return mx

def rand_keys(bits_list, seed):
    rng = random.Random(seed)
    return [rng.randrange(1 << (b - 1), 1 << b) if b > 1 else 1 for b in bits_list]

def main():
    print("\n=== FIRING CONTROL (plant d_2 = 3*d_1, must detect) ===")
    planted = [D[0], 3 * D[0] % n, D[2], D[3]]
    test_multiplier(planted, "PLANT c=3")

    print("\n=== RANDOM matched control (82 independent keys, same bit-ranges) ===")
    for seed in (1, 2):
        Rk = rand_keys(BITS, seed)
        test_multiplier(Rk, f"rand{seed}")
        test_affine(Rk, f"rand{seed}")
        test_gcd(Rk, f"rand{seed}")

    print("\n=== REAL 82 solved keys (d known, EXHAUSTIVE) -- NOTE: small keys inflate chance hits ===")
    test_multiplier(D, "REAL-82")
    test_affine(D, "REAL-82")
    test_gcd(D, "REAL-82")

    # LARGE-KEY subset (bits>=50): spurious small relations are negligible here (this is the clean test)
    Dlarge = [d for b, d in solved if b >= 50]
    bl = [b for b, _ in solved if b >= 50]
    print(f"\n=== REAL large keys only (bits>=50, {len(Dlarge)} keys) -- the CLEAN test ===")
    test_multiplier(Dlarge, "REAL-large")
    test_affine(Dlarge, "REAL-large")
    test_gcd(Dlarge, "REAL-large")
    for seed in (1, 2, 3):
        Rl = rand_keys(bl, 100 + seed)
        test_multiplier(Rl, f"rand-large{seed}")

    print("\n=== 7 unsolved exposed points: pairwise P_i=c*P_j (c<=4096, incremental) ===")
    ps = {Pt: i for i, Pt in unsolved_pts}
    h = []
    for i, Pa in unsolved_pts:
        acc = Pa
        for c in range(2, 4097):
            acc = add(acc, Pa)
            j = ps.get(acc)
            if j is not None and j != i: h.append((j, c, i))
    print(f"  [MULT unsolved-pts] {len(h)} hits {h[:3]}")

    print("\n=== VERDICT ===")
    print("  Informative iff PLANT fired and RANDOM matched none. Then the REAL 82 (full power,")
    print("  exhaustive over multipliers) either shows joint algebraic structure or matches random.")
    print("  This uses ALL 82 solved keys, not 7 -- the power the earlier test lacked.")

if __name__ == '__main__':
    main()
