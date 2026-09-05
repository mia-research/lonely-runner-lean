#!/usr/bin/env python3
"""
struct_test_harness.py  —  shared brute-forceable testbed + Test A (ladder leakage).

Plan v4, engine 0: pick a width N where the true d is KNOWABLE, build a candidate
structural feature, measure its LIFT over blind baseline, then sweep N and read the
SCALING (signal plateaus, noise decays). Verdict from integer success counts and
their N-trend -- never a float threshold. secp256k1 ops are exact ints (imported
from puzzle_kangaroo.py). z-scores are printed as a diagnostic only.

TEST A -- reverse-ladder branch predictor ("is there a Z-order-sort for the ladder?")
  MSB-first, Q = dG is R_N. Each step down, R_j = 2*R_{j-1} + b_j*G, so the two
  candidate predecessors are  half(R_j)  (hypothesis b=0) and  half(R_j - G)
  (hypothesis b=1); exactly one is the true R_{j-1}, chosen by bit b_j of d. If the
  ladder leaks, some CHEAP LOCAL feature of the candidate pair predicts b_j > 1/2.
  Matched null = 1/2 (bit is independent of any feature of a random function).
  SIGNAL: |acc - 1/2| stays bounded away from 0 as N grows (compounds to a break).
  NOISE : |acc - 1/2| ~ 1/sqrt(#decisions) -> 0.

Usage: python3 struct_test_harness.py [--M 150]
"""
import argparse, secrets, math
from puzzle_kangaroo import add, G, N_ORD, P, Gx, Gy

INV2 = (N_ORD + 1) // 2          # 2*INV2 == 1 (mod N_ORD)

def mul(k, Pt):                  # local mul (double-and-add), exact
    R = None; A = Pt; k %= N_ORD
    while k:
        if k & 1: R = add(R, A)
        A = add(A, A); k >>= 1
    return R

# The two candidate predecessors at any MSB step are exactly {R_{j-1}, R_{j-1} +/- Ghalf}
# where Ghalf = INV2*G is a FIXED point:  half(R_j - b*G) = R_{j-1} + (bit-b)*Ghalf.
# So no per-step halving is needed -- one add against a precomputed point.
GHALF = mul(INV2, G)             # (n+1)/2 * G, fixed
NEG_GHALF = (GHALF[0], (P - GHALF[1]) % P)

# ---- cheap local features of a point (x, y) -> integer scalar ----
FEATS = {
    "x_low":   lambda pt: pt[0] & 1,
    "y_low":   lambda pt: pt[1] & 1,
    "x_mod7":  lambda pt: pt[0] % 7,
    "x_ham":   lambda pt: bin(pt[0]).count("1"),
    "x_val":   lambda pt: pt[0],
    "y_ham":   lambda pt: bin(pt[1]).count("1"),
}

def decisions_for_key(d, N):
    """Walk d top-down; yield (cand0, cand1, true_bit) at each MSB step.
    Rprev = R_{j-1} is the TRUE predecessor; the decoy is Rprev +/- Ghalf.
    c0 = hypothesis bit=0, c1 = hypothesis bit=1 (one equals Rprev, one the decoy)."""
    R = None
    for j in range(N - 1, -1, -1):
        bit = (d >> j) & 1
        Rprev = R
        R = add(add(R, R), G if bit else None)          # R_j = 2 R_{j-1} + bit*G
        if Rprev is None:                                # first step: no predecessor
            continue
        if bit == 0:
            c0, c1 = Rprev, add(Rprev, NEG_GHALF)        # true=c0
        else:
            c0, c1 = add(Rprev, GHALF), Rprev            # true=c1
        if c0 is None or c1 is None:                      # identity edge; skip
            continue
        yield c0, c1, bit

def run_testA(Ns, M, seed_rng):
    print(f"# TEST A  reverse-ladder branch predictor   M={M} keys/width")
    print(f"# per feature: guess=argmax_pair(feature); acc = P(guess==true bit); null=0.5")
    print(f"# columns per width N: acc (z = (acc-.5)*sqrt(T), reported diagnostic only)\n")
    header = "  feature     " + "".join(f"{'N='+str(n):>16}" for n in Ns)
    # accumulate integer success counts
    results = {f: {} for f in FEATS}          # feature -> N -> (succ, T)
    for N in Ns:
        lo = 1 << (N - 1)
        succ = {f: 0 for f in FEATS}; T = 0
        for _ in range(M):
            d = lo + secrets.randbelow(lo)     # exact uniform in [2^{N-1}, 2^N)
            for c0, c1, bit in decisions_for_key(d, N):
                T += 1
                for f, fn in FEATS.items():
                    # predictor: guess bit=1 iff feature(c1) > feature(c0); tie -> 0
                    guess = 1 if fn(c1) > fn(c0) else 0
                    if guess == bit:
                        succ[f] += 1
        for f in FEATS:
            results[f][N] = (succ[f], T)
    print(header)
    for f in FEATS:
        cells = []
        for N in Ns:
            s, T = results[f][N]
            acc = s / T
            z = (acc - 0.5) * math.sqrt(T)             # noqa: float (reported diagnostic)
            cells.append(f"{acc:.4f}({z:+.1f})")
        print(f"  {f:<11}" + "".join(f"{c:>16}" for c in cells))
    print("\nread: acc pinned at ~0.5 with |z| NOT growing across N  => NULL (no ladder sort,")
    print("      matched to the branch decision, over this N-range).")
    print("      acc bounded away from 0.5 with |z| growing across N  => SIGNAL (escalate).")

def run_control_uniform(T):
    """DECISIVE control: Rprev drawn UNIFORM on the curve (r*G, r uniform in [1,n)).
    Same candidate/feature machinery. Theory: if the width-N bias is only the
    interval non-uniformity of Rprev (not a ladder leak), accuracy -> 0.5 here."""
    print(f"\n# CONTROL  uniform Rprev = r*G   T={T} decisions")
    print(f"# if the ladder itself leaked, features would still beat 0.5 here.\n")
    succ = {f: 0 for f in FEATS}
    for _ in range(T):
        Rprev = mul(1 + secrets.randbelow(N_ORD - 1), G)   # uniform on curve
        bit = secrets.randbelow(2)
        if bit == 0:
            c0, c1 = Rprev, add(Rprev, NEG_GHALF)
        else:
            c0, c1 = add(Rprev, GHALF), Rprev
        if c0 is None or c1 is None:
            continue
        for f, fn in FEATS.items():
            guess = 1 if fn(c1) > fn(c0) else 0
            if guess == bit:
                succ[f] += 1
    for f in FEATS:
        acc = succ[f] / T
        z = (acc - 0.5) * math.sqrt(T)                      # noqa: float (diagnostic)
        print(f"  {f:<11} acc={acc:.4f}  (z={z:+.1f})")
    print("\n  acc ~ 0.5 here => the width-N bias is the interval artifact, NOT a ladder leak.")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--M", type=int, default=150)
    ap.add_argument("--Ns", type=int, nargs="+", default=[20, 24, 28, 32])
    ap.add_argument("--control", type=int, default=0, help="run uniform-Rprev control with T decisions")
    a = ap.parse_args()
    if a.control:
        run_control_uniform(a.control)
    else:
        run_testA(a.Ns, a.M, secrets)

if __name__ == "__main__":
    main()
