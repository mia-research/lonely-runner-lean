#!/usr/bin/env python3
"""
Test the IDEA (not just the residue method): do the 82 real keys' D-SIGNATURE TERMS
have special MULTIPLICATIVE structure (small size / smoothness) — the direct
signature of a sum-of-simple-fractions construction (early D-terms = small smooth
denominators like 3,7,13) — vs random keys?

Two lenses NOT covered by the earlier residue-mod-6 test:
  (A) SIZE: bit-length of D_1..D_4. Sum-of-fractions -> tiny early terms; random ->
      early terms grow ~geometrically.
  (B) SMOOTHNESS: largest-prime-factor / B-smooth part of each D_i (trial division to
      10^6; small D_i factored fully). Sum-of-fractions early terms are perfectly
      smooth (they ARE small primes); random D_i have random smoothness.
Compare real 82 vs random-key null (matched bits) vs sum-of-fractions null.
Exact integer D-recursion; trial division exact.
"""
import csv, random
from sympy import factorint


def d_sig(N, key):
    e = abs(key); t = []
    while e > 0:
        D = N // e
        if D == 0: break
        t.append(D); e = abs(e - N // D)
    return t


def largest_pf_bounded(x, B=10**6):
    """largest prime factor of the part of x that is B-smooth; returns (lpf_small, remaining)."""
    if x <= 1: return (1, 1)
    lpf = 1; r = x
    d = 2
    while d * d <= r and d <= B:
        while r % d == 0:
            r //= d; lpf = d
        d += 1 if d == 2 else 2
    # r is now either 1, a prime >B-ish, or a product of primes >current d
    return (lpf, r)  # r>1 means a large (>reached) factor remains


def smooth_metrics(terms):
    """avg over terms: is fully B-smooth? size of large residual (bits)."""
    fully_smooth = 0; resid_bits = []
    for D in terms:
        lpf, r = largest_pf_bounded(D, 10**6)
        if r == 1:
            fully_smooth += 1; resid_bits.append(0)
        else:
            resid_bits.append(r.bit_length())
    return fully_smooth / len(terms), sum(resid_bits) / len(terms)


def sum_frac(bits, fracs, offbits, rng):
    N = 1 << bits; k = sum(N // f for f in fracs) + (rng.randrange(1 << offbits) if offbits else 0)
    return k % N


def main():
    rng = random.Random(7)
    rows = [(int(r["bits"]), int(r["private_key"], 16))
            for r in csv.DictReader(open("puzzles_verified.csv")) if int(r["bits"]) >= 20]
    print(f"D-signature multiplicative structure — {len(rows)} real keys (bits>=20)\n")

    # (A) sizes of D_1..D_4 (bit-lengths), real vs random
    def term_sizes(keyset):
        cols = [[], [], [], []]
        for bits, d in keyset:
            sig = d_sig(1 << bits, d)
            for i in range(4):
                if i < len(sig): cols[i].append(sig[i].bit_length())
        return [sum(c) / len(c) if c else 0 for c in cols]

    real = [(b, d) for b, d in rows]
    randk = [(b, (1 << (b - 1)) + rng.randrange(1 << (b - 1))) for b, d in rows for _ in range(50)]
    sfk = [(b, sum_frac(b, [3, 7, 13], b // 8, rng)) for b, d in rows for _ in range(50)]

    print("(A) mean bit-length of D_i (i=1..4):")
    print(f"    {'set':22s} D1     D2     D3     D4")
    for name, ks in [("REAL 82", real), ("random null", randk), ("sum-of-fractions", sfk)]:
        s = term_sizes(ks)
        print(f"    {name:22s} " + "  ".join(f"{x:5.1f}" for x in s))

    # (B) smoothness of the D-terms, BIT-MATCHED (fix: per real key, matched-bits nulls)
    # focus on EARLY terms D_2,D_3 (where a construction signature lives; D_1=1 trivial)
    def early_terms_bitmatched(mode):
        T = []
        for bits, d in real:
            if mode == "real":
                sig = d_sig(1 << bits, d)
            elif mode == "rand":
                sig = d_sig(1 << bits, (1 << (bits - 1)) + rng.randrange(1 << (bits - 1)))
            else:
                sig = d_sig(1 << bits, sum_frac(bits, [3, 7, 13], bits // 8, rng))
            T += sig[1:3]  # D_2, D_3
        return T
    print("\n(B) smoothness of EARLY D-terms (D_2,D_3), BIT-MATCHED nulls:")
    for name, mode in [("REAL 82", "real"), ("random null", "rand"), ("sum-of-fractions", "sf")]:
        fs, rb = smooth_metrics(early_terms_bitmatched(mode))
        print(f"    {name:22s}: fully-10^6-smooth={fs:.3f}   mean large-residual bits={rb:.1f}")

    # show a few real D-signatures for eyeball
    print("\n  sample real D-signatures (puzzle: D-terms):")
    for bits, d in real[:4] + real[-3:]:
        print(f"    {bits}b: {d_sig(1<<bits, d)}")
    print("\n  READING: if REAL matches RANDOM (D-term sizes grow, similar smoothness) and")
    print("  is UNLIKE sum-of-fractions (tiny smooth early terms), the multiplicative")
    print("  D-term structure shows NO construction signature — testing the IDEA, not just")
    print("  the residue method.")


if __name__ == "__main__":
    main()
