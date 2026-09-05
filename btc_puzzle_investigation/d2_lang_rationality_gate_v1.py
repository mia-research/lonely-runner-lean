#!/usr/bin/env python3
"""Exact well-posedness gate for the registered D2 Lang-torsor object.

The D1 lift uses C: w^4 = x^3 + 7 and, when y_P is a quadratic residue,
P^+ = (x_P, sqrt(y_P)) and P^- = (x_P, -sqrt(y_P)).  The registered D2
proposal applies the arithmetic Lang map F - 1 to [P^+ - P^-].  For points
whose coordinates lie in F_p, arithmetic Frobenius fixes each point, so the
Lang image is the zero divisor.  This script checks that premise directly.

This is a gate only.  It must not be used as an Arm A/B affinity result.
"""

from sympy import isprime


def points_e(p):
    """Return affine points on y^2 = x^3 + 7 over F_p."""
    pts = []
    for x in range(p):
        rhs = (x * x * x + 7) % p
        for y in range(p):
            if y * y % p == rhs:
                pts.append((x, y))
    return pts


def point_order(p):
    return len(points_e(p)) + 1


def liftable_rows(p):
    rows = []
    for x, y in points_e(p):
        if y == 0:
            continue
        w = next((z for z in range(p) if z * z % p == y), None)
        if w is None:
            continue
        rows.append((x, y, w, (-w) % p))
    return rows


def run(p):
    n = point_order(p)
    pts = points_e(p)
    rows = liftable_rows(p)
    fixed = 0
    lang_zero = 0
    for x, y, wp, wm in rows:
        # Arithmetic Frobenius on affine coordinates of C over F_p.
        fp_plus = (pow(x, p, p), pow(wp, p, p))
        fp_minus = (pow(x, p, p), pow(wm, p, p))
        plus = (x, wp)
        minus = (x, wm)
        if fp_plus == plus and fp_minus == minus:
            fixed += 1
        # F(P+) - P+ and F(P-) - P- are both the zero divisor termwise.
        if fp_plus == plus and fp_minus == minus:
            lang_zero += 1
    print(
        f"p={p} #E={n} prime_order={bool(isprime(n))} "
        f"affine_points={len(pts)} liftable={len(rows)} "
        f"frobenius_fixed={fixed}/{len(rows)} "
        f"lang_zero={lang_zero}/{len(rows)}"
    )
    return n, len(rows), fixed, lang_zero


def main():
    primes = [13, 43, 67, 79, 163, 349, 433]
    results = [run(p) for p in primes]
    assert all(fixed == liftable for _, liftable, fixed, _ in results)
    assert all(lang_zero == liftable for _, liftable, _, lang_zero in results)
    print("GATE: PASS -- every registered F_p-rational D1 lift is Lang-trivial")
    print("ARMS: BLOCKED -- no nonzero twisted coordinate exists in this realization")


if __name__ == "__main__":
    main()
