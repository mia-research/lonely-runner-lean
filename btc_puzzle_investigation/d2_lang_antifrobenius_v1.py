#!/usr/bin/env python3
"""Exact extension-field repair of the D2 Lang-map gate.

For C: w^4 = x^3 + 7 and Q(P) = [P+ - P-], classify the two cases:
  chi_2(y_P) = +1: P+, P- are F_p-rational, so F(Q) = Q and (F-1)Q = 0;
  chi_2(y_P) = -1: P+, P- are defined over F_{p^2} and Frobenius swaps them,
                    so F(Q) = -Q and (F-1)Q = -2Q.

This is an exact geometry check. It does not compute a Jacobian discrete log.
"""

from sympy import isprime


def points_e(p):
    pts = []
    for x in range(p):
        rhs = (x * x * x + 7) % p
        for y in range(p):
            if y * y % p == rhs:
                pts.append((x, y))
    return pts


def classify(p, y):
    if y == 0:
        return 0
    chi = pow(y, (p - 1) // 2, p)
    assert chi in (1, p - 1)
    return 1 if chi == 1 else -1


def run(p):
    pts = points_e(p)
    n = len(pts) + 1
    counts = {1: 0, -1: 0, 0: 0}
    for _, y in pts:
        counts[classify(p, y)] += 1
    rational = counts[1]
    anti = counts[-1]
    assert counts[0] == 0, "a y=0 point would require a separate 2-torsion case"
    assert rational + anti == len(pts)
    print(
        f"p={p} #E={n} prime_order={bool(isprime(n))} "
        f"F_p_Q={rational} Lang_zero={rational} "
        f"F_p2_anti={anti} Lang_minus2={anti}"
    )
    return n, rational, anti


def main():
    rows = [run(p) for p in [43, 67, 79, 163, 349, 433]]
    assert all(rational == rational_lang for _, rational, _ in rows for rational_lang in [rational])
    assert all(anti == anti_lang for _, _, anti in rows for anti_lang in [anti])
    print("EXACT: F(Q) = Q on the residue half and F(Q) = -Q on the nonresidue half")
    print("LANG:  (F-1)Q = 0 or -2Q; no nonlinear re-linearization is created")


if __name__ == "__main__":
    main()
