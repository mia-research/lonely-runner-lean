#!/usr/bin/env python3
"""
Compute the ACTUAL safe count x_0(E) for each failing test case from
lrc_prop_10_5_empirical_check.py — not just |{b in J : s_d uncovered}| but
the full safe count across B_div. This lets us distinguish:

  (a) Cases where x_0 >= phi(n) via safe fibres OUTSIDE J (the late-window
      strategy misses them but the proposition still holds) — these are
      candidates for A.4-style certified enumeration or for a different
      safe-window analysis.

  (b) Genuine counterexamples to Prop 10.5 — would invalidate the plan.

Also reports safe count in Period_1 = [L/n, 2L/n] for comparison with the
legacy Lemma 10.2 template.
"""

from __future__ import annotations

import math
from fractions import Fraction


def modinv(a: int, m: int) -> int:
    g, x, _ = _egcd(a % m, m)
    if g != 1:
        raise ValueError(f"modinv: gcd({a},{m}) = {g} != 1")
    return x % m


def _egcd(a: int, b: int):
    if b == 0:
        return a, 1, 0
    g, x1, y1 = _egcd(b, a % b)
    return g, y1, x1 - (a // b) * y1


def lcm_many(xs):
    out = 1
    for x in xs:
        out = out * x // math.gcd(out, x)
    return out


def safe_count_full(E: tuple[int, ...], n: int) -> tuple[int, int, int, int]:
    """
    Return (x_0, |B_div|, safe_in_J, safe_in_Period1) for the tuple E.
    x_0 = count of integer fibres in B_div where runner 0 is lonely.
    Since we're at discrete times k/N, the safe condition is
    (e_i k mod N) in [L, (n-1)L].  We iterate over fibres b in B_div
    and count integer k in [b*n - correction, ...] — but simpler:
    count integer fibres b such that no runner covers residue-0 "overlap",
    actually let me just do the canonical safe-fibre count:
    For each integer b in B_div, b is safe iff
    forall e in E: (e * b) mod N is in [L, (n-1)L],
    where N = n * L.
    """
    L = lcm_many(E)
    N = n * L
    Bdiv_lo = L // n if L % n == 0 else (L + n - 1) // n
    Bdiv_hi = ((n - 1) * L) // n  # inclusive
    # Safe iff for all e, (e*b) mod N in [L, (n-1)L]
    safe = 0
    for b in range(Bdiv_lo, Bdiv_hi + 1):
        ok = True
        for e in E:
            v = (e * b) % N
            if v < L or v > (n - 1) * L:
                ok = False
                break
        if ok:
            safe += 1
    Bdiv_size = Bdiv_hi - Bdiv_lo + 1

    # Period_1 = [L/n, 2L/n]
    p1_lo = Bdiv_lo
    p1_hi = (2 * L) // n
    p1_safe = 0
    for b in range(p1_lo, min(p1_hi, Bdiv_hi) + 1):
        ok = True
        for e in E:
            v = (e * b) % N
            if v < L or v > (n - 1) * L:
                ok = False
                break
        if ok:
            p1_safe += 1

    # J = [(n-2)L/(n-1), (n-1)L/n]
    from math import ceil
    J_lo_f = Fraction((n - 2) * L, n - 1)
    J_hi_f = Fraction((n - 1) * L, n)
    J_lo = -(-J_lo_f.numerator // J_lo_f.denominator) if J_lo_f.denominator != 1 else int(J_lo_f)
    J_hi = J_hi_f.numerator // J_hi_f.denominator
    J_lo = max(J_lo, Bdiv_lo)
    J_hi = min(J_hi, Bdiv_hi)
    j_safe = 0
    for b in range(J_lo, J_hi + 1):
        ok = True
        for e in E:
            v = (e * b) % N
            if v < L or v > (n - 1) * L:
                ok = False
                break
        if ok:
            j_safe += 1

    return safe, Bdiv_size, j_safe, p1_safe


# Failing cases from the previous empirical check
FAILING = [
    # (E_non, k_div, M, n, d)
    ((3, 4), 1, 7, 5, 1),
    ((3, 4), 1, 12, 5, 1),
    ((3, 4), 2, 7, 5, 1),
    ((3, 4), 2, 12, 5, 1),
    ((2, 4), 1, 8, 5, 1),
    ((2, 4), 1, 13, 5, 1),
    ((2, 4), 2, 8, 5, 1),
    ((2, 4), 2, 13, 5, 1),
    ((3, 4), 1, 11, 5, 2),
    ((3, 4), 2, 11, 5, 2),
    ((1, 4), 1, 8, 5, 2),
    ((1, 4), 2, 8, 5, 2),
    ((1, 3), 1, 9, 5, 2),
    ((1, 3), 2, 9, 5, 2),
    # Additional n=5 variations with residue 3 dropped
    ((2, 4), 1, 6, 5, 3),
    ((2, 4), 1, 11, 5, 3),
    ((2, 4), 1, 1, 5, 3),
    ((2, 4), 2, 6, 5, 3),
    ((2, 4), 2, 11, 5, 3),
    ((2, 4), 2, 1, 5, 3),
]


def main():
    print(f"{'Case':<50} {'L':>8} {'|Bdiv|':>8} {'x_0':>6} {'φ(n)':>5} {'safe_J':>8} {'safe_P1':>8} {'status'}")
    print("-" * 110)
    fails_as_prop = 0
    ok_full = 0
    for (E_non, k_div, M, n, d) in FAILING:
        E = tuple(list(E_non) + [k_div * n, M])
        if len(set(E)) != len(E):
            print(f"n={n},d={d},E_non={E_non},k={k_div},M={M}: DUP SPEEDS, skip")
            continue
        phi_n = n - 1
        x0, bdiv, jsafe, p1safe = safe_count_full(E, n)
        status = "OK" if x0 >= phi_n else "PROP 10.5 VIOLATED"
        if x0 >= phi_n:
            ok_full += 1
        else:
            fails_as_prop += 1
        L = lcm_many(E)
        name = f"n={n},d={d},E_non={E_non},k={k_div},M={M}"
        print(f"{name:<50} {L:>8} {bdiv:>8} {x0:>6} {phi_n:>5} {jsafe:>8} {p1safe:>8} {status}")
    print("-" * 110)
    print(f"Tests: {ok_full + fails_as_prop}   x_0 >= phi(n): {ok_full}   actual violations: {fails_as_prop}")
    return 0 if fails_as_prop == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
