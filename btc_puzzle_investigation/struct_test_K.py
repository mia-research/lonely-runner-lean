#!/usr/bin/env python3
"""
struct_test_K.py  —  Plan v5 Test K: DP / point-coordinate uniformity of secp256k1.

Kangaroo + distinguished-point detection assume the walk visits points whose
coordinates are effectively uniform (so DP hits are unbiased and collisions behave
birthday-like). This tests that assumption directly, at scale, on the curve itself
(unlimited data). For three incremental point streams --

  orbit   P += G            (consecutive multiples jG)
  walk    P += jumpG[X&..]  (the actual kangaroo pseudo-random jump map)
  stride  P += BIGSTEP      (large fixed decorrelating step)

-- test whether X mod m is uniform, for several m, vs a matched integer-uniform
null. Verdict by the SCALING discriminator (power_scaling.py): a real curve bias
makes the permutation rank drop AND stay dropped as N grows; noise regresses to
mid-null. chi-square is a ranked statistic vs matched null, never a table
threshold (CLAUDE.md: no float decides the verdict).

Usage: python3 struct_test_K.py
"""
import secrets
from puzzle_kangaroo import add, G, N_ORD, P

def mul(k, Pt):
    R = None; A = Pt; k %= N_ORD
    while k:
        if k & 1: R = add(R, A)
        A = add(A, A); k >>= 1
    return R

MODULI = [2, 3, 7, 17, 256, 257, 65537]
KJUMP = 16
JUMPG = [mul(1 << (i + 3), G) for i in range(KJUMP)]     # fixed jump points
BIGSTEP = mul(0x9E3779B97F4A7C15, G)                     # large decorrelating step

def stream(kind, N, start):
    """Yield N X-coords from an incremental point stream."""
    Pt = start
    for _ in range(N):
        yield Pt[0]
        if kind == "orbit":
            Pt = add(Pt, G)
        elif kind == "walk":
            Pt = add(Pt, JUMPG[Pt[0] & (KJUMP - 1)])
        else:  # stride
            Pt = add(Pt, BIGSTEP)

def chisq(counts, N, m):
    exp = N / m                                          # noqa: float (ranked statistic)
    return sum((c - exp) * (c - exp) for c in counts) / exp   # noqa: float

def rank_uniform(xs, m, B, rng_seed_bytes):
    """chi-square of (xs mod m) vs B matched integer-uniform draws. Returns (chi2, rank)."""
    N = len(xs)
    obs = [0] * m
    for x in xs:
        obs[x % m] += 1
    real = chisq(obs, N, m)
    ge = 0
    for _ in range(B):
        c = [0] * m
        for _ in range(N):
            c[secrets.randbelow(m)] += 1
        if chisq(c, N, m) >= real:
            ge += 1
    return real, ge, B

def main():
    Ns = [2000, 5000, 10000, 20000]
    B = 60
    print("# TEST K  point-coordinate uniformity (X mod m) vs matched uniform null")
    print(f"# streams: orbit(+G), walk(kangaroo jump), stride(+BIGSTEP). null draws={B}")
    print("# rank = #null chi2 >= real, out of B. uniform => rank mid-range (~B/2).")
    print("# SIGNAL: rank -> 0 AND stays there as N grows. NOISE: rank stays mid.\n")
    # fixed random starts per stream (independent points)
    starts = {k: mul(1 + secrets.randbelow(N_ORD - 1), G) for k in ("orbit", "walk", "stride")}
    for kind in ("orbit", "walk", "stride"):
        print(f"[{kind}]")
        # collect the largest N once, slice for smaller N
        xs_full = list(stream(kind, max(Ns), starts[kind]))
        for N in Ns:
            xs = xs_full[:N]
            cells = []
            for m in MODULI:
                chi, ge, b = rank_uniform(xs, m, B, None)
                cells.append(f"m{m}:{ge:>2}/{b}")
            print(f"   N={N:>6}  " + "  ".join(cells))
        print()
    print("read: ranks scattered across [0,B] with no N-trend => X mod m uniform on the")
    print("      curve (kangaroo/DP uniformity assumption holds at scale). A modulus whose")
    print("      rank -> 0 AND deepens with N would be a real coordinate bias (escalate).")

if __name__ == "__main__":
    main()
