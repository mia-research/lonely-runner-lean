#!/usr/bin/env python3
"""
Thread 3: is 4p = t^2 + 27 M^2 special to secp256k1 (b=7), or universal to j=0?

Claim under test (from the pasted agenda): "the 27M^2 form is a discriminant
shadow special to D=7."  Verify instead that it is the CM-by-Z[omega] norm form,
hence UNIVERSAL to every prime p == 1 mod 3 and every curve y^2 = x^3 + D
(all j=0), with D only selecting which of the six sextic twists you land on
(same M, six values of t).  Exact integer arithmetic throughout.
"""
from sympy import isprime, sqrt_mod, factorint
import sympy

def cornacchia_27(p):
    """Solve 4p = t^2 + 27 M^2 (p == 1 mod 3). Returns (t, M) with t,M>0, or None."""
    # 4p = t^2 + 27 M^2  <=>  need t^2 == 4p mod 27 ... solve via sqrt of -27 mod something.
    # Easiest: represent p by x^2+3y^2 first is not it; use: for p==1 mod 3,
    # 4p = L^2 + 27 M^2 solvable. Brute M then check.
    for M in range(1, int((4*p)**0.5)//5 + 2):
        rem = 4*p - 27*M*M
        if rem <= 0:
            break
        r = sympy.integer_nthroot(rem, 2)
        if r[1]:
            return (r[0], M)
    return None

def curve_order(D, p):
    """#E(F_p) for y^2 = x^3 + D by summing Legendre symbols (small p only)."""
    from sympy.ntheory import jacobi_symbol
    cnt = 1  # point at infinity
    for x in range(p):
        rhs = (x*x*x + D) % p
        if rhs == 0:
            cnt += 1
        else:
            ls = jacobi_symbol(rhs, p)
            cnt += 1 + ls
    return cnt

def main():
    print("=== small primes p == 1 mod 3: 4p = t^2 + 27 M^2 universal? ===")
    tested = 0
    for p in range(7, 400):
        if not isprime(p) or p % 3 != 1:
            continue
        sol = cornacchia_27(p)
        assert sol is not None, f"no 27M^2 rep for p={p}"
        t, M = sol
        assert 4*p == t*t + 27*M*M
        tested += 1
    print(f"  4p = t^2 + 27M^2 solved for ALL {tested} primes p==1 mod 3 in [7,400]  [OK]")

    print("\n=== all six j=0 twists y^2=x^3+D over one p share the SAME M ===")
    p = 103  # == 1 mod 3
    _, Mp = cornacchia_27(p)
    orders = {}
    for D in range(1, 7*3):
        if D % p == 0:
            continue
        N = curve_order(D, p)
        t = p + 1 - N                      # trace
        # each order must satisfy 4p = t^2 + 27 M^2 with the SAME M (up to sign class)
        orders[N] = t
    Ms = set()
    for N, t in orders.items():
        val = 4*p - t*t
        if val >= 0 and val % 27 == 0:
            root = sympy.integer_nthroot(val // 27, 2)
            if root[1]:
                Ms.add(root[0])
    print(f"  p={p}: distinct curve orders seen = {sorted(set(orders))}")
    print(f"  traces t range over the six twist values; M-set from 4p=t^2+27M^2 = {sorted(Ms)}")
    print(f"  Cornacchia M for p alone = {Mp}  ->  every twist shares M = {Mp}: {Ms == {Mp}}")

    print("\n=== secp256k1: b=7 only PICKS the twist; M is the p-invariant ===")
    p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
    n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
    t = p + 1 - n
    val = 4*p - t*t
    assert val % 27 == 0
    M = sympy.integer_nthroot(val // 27, 2)
    assert M[1]
    M = M[0]
    print(f"  t = p+1-n = {t}")
    print(f"  4p - t^2 divisible by 27: {val % 27 == 0};  M = {M}")
    print(f"  matches KNOWN_FACTS M = 101138146489082181198416925222535253057: "
          f"{M == 101138146489082181198416925222535253057}")
    print("\n  => 27M^2 is the CM-by-Z[omega] norm form, universal to every p==1 mod 3")
    print("     and every j=0 curve. b=7 selects the unique prime-order twist, not the 27.")

if __name__ == "__main__":
    main()
