#!/usr/bin/env python3
"""Shared, exact harness for testing GLM's flap<->quadratic-residue claim
against the repo's CANONICAL lift/flap definitions.

Uses int1_frame_operator_v1.build(p) -> (eis, eps)  [the master's canonical pair]
and enorm from lift_sextant_rhombus_law_proof_v2.  Exact integer arithmetic only
(no float in the signal path), per btc_puzzle_investigation/CLAUDE.md.

GLM's claim (stated neutrally, to be tested):
  (A) identity:   N(eis(x)) equals the least positive residue of x^2 mod p,
                  and in particular  N(eis(x)) == x^2 (mod p).
  (B) threshold:  eps(x)=0 (core)  <=>  N(eis(x)) < 3p/16   (an iff).
  (C) thesis:     eps is an ARITHMETIC object -- it carries information about a
                  multiplicative character / residue-symbol of x.
"""
import sys
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import enorm
from glv_fundamental_domain_law_v1 import cube_roots


def leg(x, p):
    """Legendre symbol chi2(x) in {-1,0,1} via Euler, exact."""
    if x % p == 0:
        return 0
    return 1 if pow(x % p, (p - 1) // 2, p) == 1 else -1


def part_A(p):
    """Deterministic identity check: is N(eis(x)) = x^2 mod p ? (GLM step A)"""
    eis, eps = build(p)
    b1, b2 = cube_roots(p)  # the two embeddings omega -> b1, b2 of Z[w]/(p)
    cong_hits = 0          # N(z) == x^2 (mod p)
    literal_hits = 0       # N(z) == (x^2 mod p) as integers (least residue)
    xyprime_hits = 0       # N(z) == x * y'  (mod p), the CORRECT formula
    n_small_disagree = 0   # cases distinguishing "size of x^2" from N(z)
    total = 0
    for x in range(1, p):
        z = eis(x)
        u, v = z
        Nz = enorm(z)                      # exact integer in [0, ~0.75 p]
        x2 = (x * x) % p                   # least positive residue of x^2
        # which embedding does eis land x under?  u+v*b == x for one of b1,b2
        emb1 = (u + v * b1) % p
        emb2 = (u + v * b2) % p
        if emb1 == x % p:
            yprime = emb2
        elif emb2 == x % p:
            yprime = emb1
        else:
            yprime = None                  # (shouldn't happen)
        cong_hits += (Nz % p == x2)
        literal_hits += (Nz == x2)
        if yprime is not None:
            xyprime_hits += (Nz % p == (x * yprime) % p)
        total += 1
    return dict(p=p, total=total,
               cong_frac=cong_hits / total,
               literal_frac=literal_hits / total,
               xyprime_frac=xyprime_hits / total)


if __name__ == "__main__":
    for p in [100003, 100057, 1000003]:
        r = part_A(p)
        print(f"p={r['p']:>8}  N(eis x) == x^2 (mod p): {r['cong_frac']:.6f}   "
              f"N == least-residue(x^2) literally: {r['literal_frac']:.6f}   "
              f"N == x*y' (mod p) [correct formula]: {r['xyprime_frac']:.6f}")
    print()
    print("Interpretation: cong_frac ~ 1/p (chance) => GLM identity FALSE;")
    print("                xyprime_frac == 1.0     => N(eis x) = x*y' (y'=other embedding), not x^2.")
