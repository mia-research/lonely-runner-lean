#!/usr/bin/env python3
"""
struct_test_E.py  —  Plan v4 Test E: cross-key generator structure (nonce/RNG bias).

Does the sequence of solved puzzle keys #1..130 look like consecutive draws from
ONE weak/linear PRNG stream (exploitable) or independent secure random (not)?

Coordinate: each key d_i in [2^{i-1}, 2^i) -> offset o_i = d_i - 2^{i-1} ->
normalized top-32-bit word  w_i = (o_i << 32) // 2^{i-1}  (exact integer; the top
bits of the "position in range" the puzzle is described by -- see u_position col).
If keys were made as  pos = lo + floor(rng_uniform * range),  the w_i ARE the top
32 bits of consecutive RNG outputs.

Detectors (all exact / integer):
  (1) GF(2) rank of the word-bit matrix and of the affine-recurrence matrix
      [w_i | w_{i+1} | 1]  -> catches LFSR / LCG-mod-2^k structure.
  (2) Berlekamp-Massey linear complexity of the LSB sequence -> LFSR length.
  (3) Serial rank (Spearman-style, integer) correlation of consecutive w_i -> LCG.

Controls: MT19937 stream (one 32-bit word/key) and secrets (crypto random).

HONEST SCOPE: with only ~82 milestone keys (2624 bits) these detect small linear
generators and LCGs. Full MT19937 state recovery needs >=624 consecutive full
words, which the sparse milestone keys do NOT provide -- so a null here rules out
weak/linear generators, NOT a correctly-seeded MT19937.

Usage: python3 struct_test_E.py
"""
import csv, secrets, random

def load_words():
    """Return list of (bits, w32) for solved keys with range size > 1."""
    out = []
    with open("solved_puzzles_xy.csv") as f:
        for row in csv.DictReader(f):
            pk = row["private_key"].strip()
            if not pk:
                continue
            d = int(pk, 16) if pk.lower().startswith("0x") else int(pk)
            i = int(row["bits"])
            if i < 2:
                continue
            lo = 1 << (i - 1)
            o = d - lo
            w = (o << 32) // lo                      # top 32 bits of position, exact
            out.append((i, w & 0xFFFFFFFF))
    return out

# ---------- (1) GF(2) rank ----------
def gf2_rank(rows):
    basis = []
    for r in rows:
        for b in basis:
            r = min(r, r ^ b)
        if r:
            basis.append(r)
            basis.sort(reverse=True)
    return len(basis)

def rank_tests(words):
    ws = [w for _, w in words]
    n = len(ws)
    r_words = gf2_rank(ws)                                   # 32-col matrix
    aff = [(ws[i] << 33) | (ws[i + 1] << 1) | 1 for i in range(n - 1)]  # [w_i|w_{i+1}|1]
    r_aff = gf2_rank(aff)
    return n, r_words, r_aff

# ---------- (2) Berlekamp-Massey over GF(2) ----------
def berlekamp_massey(bits):
    C = [1]; B = [1]; L = 0; m = 1; b = 1
    for n in range(len(bits)):
        d = bits[n]
        for i in range(1, L + 1):
            d ^= C[i] * bits[n - i]
        if d == 0:
            m += 1
        elif 2 * L <= n:
            T = C[:]
            while len(C) < len(B) + m:
                C.append(0)
            for i in range(len(B)):
                C[i + m] ^= B[i]
            L = n + 1 - L; B = T; b = d; m = 1
        else:
            while len(C) < len(B) + m:
                C.append(0)
            for i in range(len(B)):
                C[i + m] ^= B[i]
            m += 1
    return L

# ---------- (3) serial rank correlation (integer) ----------
def serial_concordance(ws):
    """Kendall-style: fraction of consecutive-pair comparisons that are concordant
    with the pair one step later. Integer counts; ~0.5 for independent."""
    n = len(ws); conc = 0; tot = 0
    for i in range(n - 2):
        a = (ws[i + 1] > ws[i]); b = (ws[i + 2] > ws[i + 1])
        tot += 1; conc += (a == b)
    return conc, tot

def summarize(name, ws):
    n = len(ws)
    r_words = gf2_rank(ws)
    aff = [(ws[i] << 33) | (ws[i + 1] << 1) | 1 for i in range(n - 1)]
    r_aff = gf2_rank(aff)
    lc = berlekamp_massey([w & 1 for w in ws])
    conc, tot = serial_concordance(ws)
    print(f"  {name:<14} n={n:3d}  GF2rank(words)={r_words:2d}/32  "
          f"GF2rank(affine)={r_aff:2d}/{min(n-1,65)}  BM(LSB)={lc:2d}/~{n//2}  "
          f"serial_conc={conc}/{tot}")

def main():
    real = load_words()
    ws_real = [w for _, w in real]
    bitslist = [i for i, _ in real]
    n = len(ws_real)
    print("# TEST E  cross-key generator structure\n")
    print(f"  loaded {n} solved keys (bits {min(bitslist)}..{max(bitslist)})")
    print("  detectors: full GF2 rank / BM~n/2 / serial_conc~n/3 (iid null) => NO linear structure\n")
    summarize("REAL keys", ws_real)
    # MT19937 stream control (Python random): one 32-bit word per key
    random.seed(20260708)
    summarize("MT19937 ctrl", [random.getrandbits(32) for _ in range(n)])
    # crypto-random control
    summarize("secrets ctrl", [secrets.randbits(32) for _ in range(n)])
    # positive control: a small LCG (should be caught: low BM / rank deficiency)
    a, c, mod = 1103515245, 12345, 1 << 31
    x = 1; lcg = []
    for _ in range(n):
        x = (a * x + c) % mod; lcg.append(x)          # x in [0,2^31): low bits linearly related
    summarize("LCG positive", lcg)
    print("\n  read: REAL matching the MT/secrets controls (full rank, BM~n/2, conc~n/3)")
    print("        => no weak/linear generator detectable. LCG row should stand out.")
    print("  SCOPE: null here rules out LFSR/LCG-class generators, NOT a seeded MT19937")
    print("         (that needs >=624 consecutive full words; 82 milestone keys can't).")

if __name__ == "__main__":
    main()
