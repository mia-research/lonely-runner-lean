#!/usr/bin/env python3
"""
frontier_beyond_singlex_v1.py

This script verifies a short list of EXACT integer facts. It proves nothing about
"closure" of either frontier.

Frontier 1 (joint / multi-point across keys) is NOT proved: the only established input
is the CITED equidistribution of single-x marginals for independent keys from ranges
>> sqrt(p) (Weil / Kohel-Shparlinski). Joint exploitability and dependent-key
detectability are open. (An earlier finite-sample MI "demonstration" was removed as a
scoped null, not a proof.)

Frontier 2 (y / group-law) -- VERIFIED here (exact integers):
  N(pi_p) = p ;  N(pi_p - 1) = n (group order) ;  trace t = p+1-n ;
  GLV [omega] fixes y (phi(x,y)=(beta x,y), x^3+7 invariant) ; y-parity flips d<->n-d.
NOT proved (cited / argued only, no closure):
  * E(F_p) ~ Z[omega]/(pi_p - 1) as Z[omega]-modules -- only the ORDER is checked here
    (necessary, not sufficient); the isomorphism is cited CM theory (Deuring).
  * "computing the linear lift Lambda = the DLP" is a REDUCTION (Lambda efficiently
    computable => d recoverable => DLP solved), so it reduces the y-lift question to the
    DLP, whose hardness is ITSELF UNPROVEN. A reduction to a conjecture, not a proof.
"""
from ecc_secp256k1 import P as p, N_ORDER as n, scalar_mul

aP = 367917413016453100223835821029139468249
bP = 303414439467246543595250775667605759171


def emul(A, B):
    a, b = A; c, d = B; return (a * c - b * d, a * d + b * c + b * d)
def enorm(w): return w[0] * w[0] - w[0] * w[1] + w[1] * w[1]


def frontier2_facts():
    print("=" * 70)
    print("Frontier 2: y / group-law -- EXACT facts (verified); NO closure claim")
    print("=" * 70)
    pi = (aP, bP)
    print(f"  N(pi_p) = p : {enorm(pi) == p}")
    nm1 = enorm((pi[0] - 1, pi[1]))
    print(f"  N(pi_p - 1) = n (group order) : {nm1 == n}")
    print(f"  Frobenius trace t = p+1-n = {p + 1 - n}")
    g = 2
    while pow(g, (p - 1) // 3, p) == 1: g += 1
    beta = pow(g, (p - 1) // 3, p)
    x1, y1 = scalar_mul(12345); xn, yn = scalar_mul((n - 12345) % n)
    print(f"  GLV [omega] fixes y (x^3+7 invariant) : {(pow(beta * x1 % p, 3, p) + 7) % p == (pow(x1, 3, p) + 7) % p}")
    print(f"  y-parity flips under d<->n-d (x equal) : {(y1 & 1) != (yn & 1) and x1 == xn}")
    print("  NOT proved here: E(F_p) ~ Z[omega]/(pi_p-1) (only the order is checked; iso is")
    print("  cited CM theory), and 'linear lift = DLP' is a REDUCTION to the DLP, whose")
    print("  hardness is unproven. No closure of the y / group-law side is claimed.\n")


if __name__ == "__main__":
    frontier2_facts()
