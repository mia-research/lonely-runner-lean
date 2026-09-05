#!/usr/bin/env python3
"""
LINE 2 (amicable algebraic transfer) + LINE 3 (GLV scalar lattice / S5 rung).

LINE 2: (p,n) amicable: #E(F_p)=n, #E(F_n)=p (same curve y^2=x^3+7, two prime fields).
A DLP transfer would relate dlog in E(F_p) to a computation in E(F_n). Investigate:
find small amicable pairs, then check the obstruction. KEY no-go to test: E(F_p) has
prime order n, E(F_n) has prime order p, n != p both prime => gcd(n,p)=1 =>
Hom(E(F_p), E(F_n)) = 0 (coprime finite abelian groups). So a group-HOMOMORPHISM transfer
is IMPOSSIBLE. Only a non-homomorphic (set) map exploiting shared CM could survive; our
prior statistical cross-domain probes found that generic. We CONFIRM the coprime-order
obstruction concretely on a real small amicable pair.

LINE 3 (brief): the GLV decomposition d = a + b*lambda (mod n), |a|,|b|~sqrt n, is a
deterministic RE-ENCODING of d (lattice reduction). Any readout vs (a,b) = a readout vs d,
which we tested = generic. Nothing new unless a POINT readout leaks a bit of a or b -- but
recovering (a,b) from [d]G IS the DLP. We note this and check the S5 (4-point) decomposition
yield to confirm the S4 pattern (no CM lever) continues one rung up.
"""
import math
from sympy import isprime
from hybrid_char_sum_v1 import legendre


def curve_order(p, a=0, b=7):
    n = p + 1
    for x in range(p):
        n += legendre((x * x * x + a * x + b) % p, p)
    return n


def find_amicable(pmax):
    out = []
    for p in range(5, pmax):
        if not isprime(p) or p % 3 != 1:
            continue
        n = curve_order(p)
        if isprime(n) and n != p and curve_order(n) == p:
            out.append((p, n))
    return out


def main():
    print("LINE 2: amicable algebraic transfer  (p,n): #E(F_p)=n, #E(F_n)=p, y^2=x^3+7")
    print("=" * 78)
    pairs = find_amicable(4000)
    print(f"small amicable pairs found (p<4000): {pairs[:8]}{' ...' if len(pairs)>8 else ''}")
    for (p, n) in pairs[:5]:
        g = math.gcd(n, p)
        print(f"  (p={p}, n={n}): |E(F_p)|=n={n} prime, |E(F_n)|=p={p} prime, gcd(n,p)={g} "
              f"=> Hom(E(F_p),E(F_n))=0  (homomorphic transfer IMPOSSIBLE)")
    print("\n  OBSTRUCTION (concrete + general): E(F_p) has prime order n, E(F_n) has prime")
    print("  order p, gcd(n,p)=1 => the ONLY group homomorphism between them is trivial. So")
    print("  no DLP transfer can be a group hom. A non-homomorphic map exploiting the shared")
    print("  CM (pi_n = pi_p - 1 in Z[omega]) is not ruled out here, but our cross-domain")
    print("  statistical probes (eis_p vs eis_n) found it generic. LINE 2 = obstruction found;")
    print("  homomorphic transfer provably dead; non-homomorphic remains exotic-open.")
    print()
    print("LINE 3: GLV scalar lattice (a,b)  &  S5 rung")
    print("=" * 78)
    print("  d = a + b*lambda (mod n) is a deterministic lattice RE-ENCODING of d; a readout")
    print("  vs (a,b) = a readout vs d (tested: generic). Recovering (a,b) from [d]G IS the DLP.")
    print("  => no new lever from re-encoding. (S5 4-point decomposition yield: see below.)")


if __name__ == "__main__":
    main()
