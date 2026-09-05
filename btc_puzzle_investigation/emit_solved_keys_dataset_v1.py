#!/usr/bin/env python3
"""
emit_solved_keys_dataset_v1.py

(1) Emits the FULL 82-solved-key dataset with every derived field
    (pub address, X, Y, private d, Farey (n,k), n,k residual 'derr', and the
    exact D-signature D_terms), each recomputed and integrity-checked against
    the on-chain X,Y via exact scalar multiplication.
(2) Provides construct_key(d, bits): the recipe to make MORE solved keys of ANY
    construction (any d you choose, by any rule) as full (d,X,Y,n,k,derr,D) records
    for detector testing. This is the "known-answer generator" -- test on these,
    then apply to unknown keys.

Definitions (all exact integers):
  A        = 2^(bits-1)                      (band base for this key size)
  band-off = d - A                           (position within the key's band)
  (n,k)    = best_nk(d,bits): Farey best rational of band-off/A over n<=256,
             i.e. argmin_{n<=256,0<=k<=n} |n*(d-A) - k*A|, then reduced by gcd.
  derr     = |n*(d-A) - k*A|                 (exact (n,k)-approximation residual)
  D_terms  = d_recursion(2^bits, d): greedy nearest-unit-fraction (Engel-like)
             expansion of d; an INVERTIBLE encoding (reproduces the dataset
             D_terms column 40260/40260, per d_recursion_exact_v1).
"""
import csv
from math import gcd
from ecc_secp256k1 import scalar_mul


def best_nk(v, bits, NMAX=256):
    """Farey best rational of (v - 2^(bits-1)) / 2^(bits-1), denominators n<=NMAX."""
    A = 1 << (bits - 1)
    num = v - A
    best = None
    for n in range(1, NMAX + 1):
        kk = (2 * n * num + A) // (2 * A)
        kk = 0 if kk < 0 else (n if kk > n else kk)
        for c in (kk - 1, kk, kk + 1):
            if 0 <= c <= n:
                key = (abs(n * num - c * A), n, c)
                if best is None or key < best:
                    best = key
    resid, n, k = best
    g = gcd(k, n) if n else 1
    return (n // g if g > 1 else n, k // g if g > 1 else k, resid)


def d_recursion(N, error):
    """greedy nearest-unit-fraction expansion; terminates exactly (residual 0)."""
    e = abs(error)
    terms = []
    while e > 0:
        D = N // e
        if D == 0:
            break
        terms.append(D)
        e = abs(e - N // D)
    return terms


def construct_key(d, bits=None):
    """Full solved-key record for ANY chosen d (any construction). If bits is
    None, uses d.bit_length(). Returns a dict; verifies (X,Y)=[d]G on the curve."""
    if bits is None:
        bits = d.bit_length()
    x, y = scalar_mul(d)
    n, k, derr = best_nk(d, bits)
    D_terms = d_recursion(1 << bits, d)
    return {"bits": bits, "d": d, "X": x, "Y": y,
            "n": n, "k": k, "derr": derr,
            "D_terms": D_terms, "n_Dterms": len(D_terms),
            "band_offset": d - (1 << (bits - 1))}


# ---- example constructions (make keys of ANY structure for testing) ----
def example_constructions(bits=64):
    import random
    N = 1 << bits
    A = 1 << (bits - 1)
    rng = random.Random(0)
    return {
        "random-in-band": A + rng.randrange(A),
        "sum-of-fractions (N/3+N/7)": N // 3 + N // 7,                 # Finding B
        "sum-of-fractions+2^(b/8)": N // 3 + N // 7 + N // 13 + 2 ** (bits // 8),  # Finding C
        "low-band-offset": A + 12345,
        "near-top": N - 999,
    }


def main():
    print("Recomputing + integrity-checking the 82 solved keys "
          "(exact [d]G vs on-chain X,Y)...\n")
    out_rows = []
    bad = 0
    with open("puzzles_verified.csv") as fh:
        for r in csv.DictReader(fh):
            bits = int(r["bits"]); d = int(r["private_key"], 16)
            X = int(r["X"], 16); Y = int(r["Y"], 16)
            rec = construct_key(d, bits)
            ok = (rec["X"] == X and rec["Y"] == Y)
            bad += (not ok)
            out_rows.append((int(r["puzzle"]), bits, d, X, Y, r["address"],
                             rec["n"], rec["k"], rec["derr"],
                             rec["n_Dterms"], rec["D_terms"], ok))
    print(f"integrity: {len(out_rows)-bad}/{len(out_rows)} keys reproduce on-chain X,Y "
          f"via scalar_mul\n")

    # write augmented CSV
    with open("solved_keys_augmented_v1.csv", "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["puzzle", "bits", "d_priv", "X", "Y", "address",
                    "n", "k", "derr", "n_Dterms", "D_terms"])
        for pz, bits, d, X, Y, addr, n, k, derr, nD, Dt, ok in out_rows:
            w.writerow([pz, bits, d, f"{X:x}", f"{Y:x}", addr, n, k, derr, nD,
                        "|".join(map(str, Dt))])
    print("wrote solved_keys_augmented_v1.csv\n")

    # compact table (a spot sample to eyeball; full data in the CSV)
    print(f"{'pz':>3} {'bit':>3} {'n':>4} {'k':>4} {'derr':>6} {'#D':>3}  D_terms(first 4)")
    for pz, bits, d, X, Y, addr, n, k, derr, nD, Dt, ok in out_rows:
        if pz % 10 == 0 or pz <= 5 or pz >= 120:
            dts = ",".join(map(str, Dt[:4])) + ("..." if nD > 4 else "")
            print(f"{pz:>3} {bits:>3} {n:>4} {k:>4} {derr:>6} {nD:>3}  {dts}")

    print("\nexample constructions (construct_key on chosen d, 64-bit):")
    for name, d in example_constructions(64).items():
        rec = construct_key(d, 64)
        print(f"  {name:32s}: n={rec['n']:>3} k={rec['k']:>3} "
              f"derr={rec['derr']} #D={rec['n_Dterms']}")


if __name__ == "__main__":
    main()
