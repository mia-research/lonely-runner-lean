#!/usr/bin/env python3
"""
evaluate_dsig_residue_claim_v1.py

Fair, rigorous check of another session's claim:
  (A) sum-of-fractions keys ([3,7,13]) give D-terms avoiding residues 3,4,5 mod 6
      (distribution 33:33:33:0:0:0 over first-3 terms) -> "avoids 3,4,5 = mu6 core".
  (B) a "construction signature" detectable in the real 82 keys (test "not yet run").
  (C) connects to mu6 = Aut(E).

Tests here:
  1. REPRODUCE (A) for [3,7,13].
  2. ROBUSTNESS: is "avoid 3,4,5 mod 6" a UNIVERSAL sum-of-fractions law, or specific
     to the denominators {3,7,13}? Vary the denominator set. If the avoided residues
     CHANGE with the denominators, the "mu6 core" reading (C) is denominator artifact,
     not curve structure.
  3. DECISIVE (B): run the D-signature on the REAL 82 keys and ask which null they
     match -- random-key D-terms or structured D-terms. This is the probe they flagged
     but did not run. We CAN run it (puzzles_verified.csv on disk).
  Exact integer D-recursion; scipy only for reporting chi-square.
"""
import csv, random
from collections import Counter
from scipy.stats import chisquare


def d_recursion(N, key):
    e = abs(key); terms = []
    while e > 0:
        D = N // e
        if D == 0: break
        terms.append(D); e = abs(e - N // D)
    return terms


def sum_frac_key(bits, fracs, offbits=32, rng=random):
    N = 1 << bits
    k = sum(N // f for f in fracs)
    if offbits: k += rng.randrange(1 << offbits)
    return k % N


def resid_hist(terms):
    c = Counter(t % 6 for t in terms); tot = len(terms)
    return [c[r] / tot for r in range(6)], [c[r] for r in range(6)]


def main():
    rng = random.Random(42)

    print("=" * 70)
    print("1. REPRODUCE (A): [3,7,13] structured keys, first-3 D-terms mod 6")
    print("=" * 70)
    terms = []
    for _ in range(5000):
        terms += d_recursion(1 << 256, sum_frac_key(256, [3, 7, 13], 32, rng))[:3]
    frac, _ = resid_hist(terms)
    print("  residue mod6:", [f"{r}:{frac[r]:.3f}" for r in range(6)])
    print(f"  avoid(3,4,5) = {frac[3]+frac[4]+frac[5]:.3f}  (claim: ~0)")

    print("\n" + "=" * 70)
    print("2. ROBUSTNESS: does the AVOIDED residue set depend on the denominators?")
    print("   (if yes, the 'mu6 core' reading is a denominator artifact, not curve)")
    print("=" * 70)
    for fracs in ([3, 7, 13], [5, 11, 17], [3, 5, 7], [7, 11, 19], [2, 3, 5], [11, 23, 41]):
        terms = []
        for _ in range(3000):
            terms += d_recursion(1 << 256, sum_frac_key(256, fracs, 32, rng))[:3]
        frac, _ = resid_hist(terms)
        avoided = [r for r in range(6) if frac[r] < 0.02]
        enriched = [r for r in range(6) if frac[r] > 0.20]
        print(f"  denom {str(fracs):16s}: mod6 {[f'{frac[r]:.2f}' for r in range(6)]}"
              f"  avoided={avoided} enriched={enriched}")

    print("\n" + "=" * 70)
    print("3. DECISIVE (B): the REAL 82 keys vs random-key and structured nulls")
    print("=" * 70)
    rows = [(int(r["bits"]), int(r["private_key"], 16))
            for r in csv.DictReader(open("puzzles_verified.csv"))]
    # real keys: first-3 D-terms mod6, using each key's NATIVE bit-length N
    real_terms = []
    for b, d in rows:
        real_terms += d_recursion(1 << b, d)[:3]
    # random null: random keys of the SAME bit-lengths
    rand_terms = []
    for b, d in rows:
        for _ in range(200):
            real_b = (1 << (b - 1)) + rng.randrange(1 << (b - 1)) if b > 1 else 1
            rand_terms += d_recursion(1 << b, real_b)[:3]
    # structured null: sum-of-fractions of the same bit-lengths
    struct_terms = []
    for b, d in rows:
        for _ in range(200):
            if b >= 8:
                struct_terms += d_recursion(1 << b, sum_frac_key(b, [3, 7, 13], b // 8, rng))[:3]
    fr_real, ct_real = resid_hist(real_terms)
    fr_rand, _ = resid_hist(rand_terms)
    fr_str, _ = resid_hist(struct_terms)
    print(f"  {'res':>3} | {'REAL-82':>9} | {'random-null':>11} | {'structured-null':>15}")
    for r in range(6):
        print(f"  {r:>3} | {fr_real[r]:>9.3f} | {fr_rand[r]:>11.3f} | {fr_str[r]:>15.3f}")
    print(f"  avoid(3,4,5):  REAL={fr_real[3]+fr_real[4]+fr_real[5]:.3f}  "
          f"random={fr_rand[3]+fr_rand[4]+fr_rand[5]:.3f}  "
          f"structured={fr_str[3]+fr_str[4]+fr_str[5]:.3f}")
    # which null does REAL match? chi-square of REAL counts vs each null's proportions
    n_real = len(real_terms)
    exp_rand = [fr_rand[r] * n_real for r in range(6)]
    exp_str = [max(fr_str[r] * n_real, 1e-9) for r in range(6)]
    chi_r = sum((ct_real[r] - exp_rand[r]) ** 2 / exp_rand[r] for r in range(6) if exp_rand[r] > 0)
    chi_s = sum((ct_real[r] - exp_str[r]) ** 2 / exp_str[r] for r in range(6))
    print(f"\n  REAL-82 fit: chi2 vs random-null = {chi_r:.1f}   vs structured-null = {chi_s:.1f}")
    print(f"  (lower = better fit; REAL matching random-null => NOT sum-of-fractions built)")
    print(f"  n(real D-terms) = {n_real}  (82 keys x first-3, minus short sigs)")


if __name__ == "__main__":
    main()
