#!/usr/bin/env python3
"""
anew_d1_forced_check_v1.py -- exact, no float.

Does the n-visibility gate FORCE M18's measured null (D1's lift 0/666 additive,
0/339 affine, at p in {43, 67, 79})?

If ell | #E(F_p) but ell does NOT divide #A_new(F_p), then NO nonzero additive
map <G_ell> -> A_new(F_p) exists at all -- so a measured "not additive" at that
prime carries ZERO information about whether some OTHER lift could be additive.
That is the difference between a measured null and a forced one, and the drill
rule says forced hits must not be banked.

Everything exact: brute-force point counts, integer arithmetic only.
F_{p^2} = F_p[t]/(t^2+1), valid since p = 3 mod 4.
"""

from math import gcd
from sympy import factorint

B = 7  # the secp cubic: E: y^2 = x^3 + 7,  C: w^4 = x^3 + 7


def count_E(p):
    """#E(F_p) for y^2 = x^3 + B, including the point at infinity."""
    squares = {}
    for y in range(p):
        squares.setdefault((y * y) % p, 0)
        squares[(y * y) % p] += 1
    return 1 + sum(squares.get((x * x * x + B) % p, 0) for x in range(p))


def count_C_Fp(p):
    """#C(F_p) for w^4 = x^3 + B.  gcd(4,3)=1 so infinity is one point."""
    fourth = {}
    for w in range(p):
        v = pow(w, 4, p)
        fourth[v] = fourth.get(v, 0) + 1
    return 1 + sum(fourth.get((x * x * x + B) % p, 0) for x in range(p))


class F2:
    """F_{p^2} = F_p[t]/(t^2+1), elements (a, b) = a + b t.  p = 3 mod 4."""

    def __init__(self, p):
        assert p % 4 == 3
        self.p = p

    def mul(self, u, v):
        p = self.p
        a, b = u
        c, d = v
        return ((a * c - b * d) % p, (a * d + b * c) % p)

    def pow(self, u, e):
        r = (1, 0)
        while e:
            if e & 1:
                r = self.mul(r, u)
            u = self.mul(u, u)
            e >>= 1
        return r

    def elements(self):
        for a in range(self.p):
            for b in range(self.p):
                yield (a, b)


def count_C_Fp2(p):
    F = F2(p)
    fourth = {}
    for w in F.elements():
        v = F.pow(w, 4)
        fourth[v] = fourth.get(v, 0) + 1
    tot = 1
    for x in F.elements():
        x3 = F.mul(F.mul(x, x), x)
        rhs = ((x3[0] + B) % p, x3[1])
        tot += fourth.get(rhs, 0)
    return tot


def main():
    print("=" * 74)
    print("Is M18's measured null FORCED by the n-visibility gate?")
    print("(exact brute force; E and C over F_p and F_{p^2})")
    print("=" * 74)
    for p in (43, 67, 79):
        nE = count_E(p)
        a_p = p + 1 - nE
        cp = count_C_Fp(p)
        cp2 = count_C_Fp2(p)
        # T1 (record RESULT_anew_identification_v1 §2): #C(F_p) = p+1-a_p
        t1 = (cp == p + 1 - a_p)
        # T2: #C(F_p^2) = p^2 + 1 - a_p^2 + 2p + 2S,  b_2 = S
        num = cp2 - (p * p + 1) + a_p * a_p - 2 * p
        assert num % 2 == 0, "S not an integer -- formula misuse"
        S = num // 2
        assert S % p == 0, f"b2 not divisible by p at p={p}: S={S}"
        m = S // p
        nA = 1 + S + p * p                      # #A_new(F_p) = P(1)
        print(f"\np = {p}")
        print(f"  #E(F_p)        = {nE}   (a_p = {a_p})")
        print(f"  T1 #C(F_p)=p+1-a_p : {'PASS' if t1 else 'FAIL'}   "
              f"[record's instrument check, reproduced]")
        print(f"  b2 = S = {S} = {m} * p    ->  m = {m}")
        print(f"  #A_new(F_p)    = 1 + m*p + p^2 = {nA}")
        print(f"  gcd(#E, #A_new) = {gcd(nE, nA)}")
        fE = factorint(nE)
        shared, unshared = [], []
        for ell in fE:
            (shared if nA % ell == 0 else unshared).append(ell)
        print(f"  primes ell | #E(F_p) : {sorted(fE)}")
        print(f"    ell that ALSO divide #A_new(F_p) : {sorted(shared)}")
        print(f"    ell that do NOT   (additive lift forced to be zero) : "
              f"{sorted(unshared)}")
        big = max(fE)
        verdict = ("FORCED zero" if nA % big else "NOT forced -- a nonzero "
                                                 "additive map could exist")
        print(f"  largest prime factor of #E is {big}: additive lift is "
              f"{verdict}")

    print("\n" + "=" * 74)
    print("READ: where the largest ell does not divide #A_new(F_p), M18's")
    print("'not additive' at that prime is FORCED by group order alone and")
    print("carries no information about other lift constructions.")


if __name__ == "__main__":
    main()
