#!/usr/bin/env python3
"""
CORRECTED empirical check for Prop 10.5:
x_0(E) = #{k in [1, N-1] : (e_i * k mod N) in [L, (n-1)L] for all e_i in E}.

Tests prime-n Case-2 tuples |E_div|=1 with one dropped unit. Success = x_0 >= phi(n).
Also reports the late-window J-count and Period_1 counts as sufficient-witness
diagnostics (useful for Lemma 10.2' proof design).
"""

from __future__ import annotations
import itertools, math
from fractions import Fraction

def lcm_many(xs):
    out = 1
    for x in xs:
        out = out * x // math.gcd(out, x)
    return out

def x0_full(E, n):
    L = lcm_many(E)
    N = n * L
    lo, hi = L, (n - 1) * L
    count = 0
    for k in range(1, N):
        ok = True
        for e in E:
            v = (e * k) % N
            if v < lo or v > hi:
                ok = False
                break
        if ok:
            count += 1
    return count, L

def j_safe_count(E, n):
    """Safe integer-fibre count within J = [(n-2)L/(n-1), (n-1)L/n] ∩ B_div."""
    L = lcm_many(E)
    N = n * L
    lo = Fraction((n - 2) * L, n - 1)
    hi = Fraction((n - 1) * L, n)
    j_lo = -(-lo.numerator // lo.denominator) if lo.denominator != 1 else int(lo)
    j_hi = hi.numerator // hi.denominator
    bdiv_lo = (L + n - 1) // n if L % n != 0 else L // n
    bdiv_hi = ((n - 1) * L) // n
    j_lo = max(j_lo, bdiv_lo)
    j_hi = min(j_hi, bdiv_hi)
    count = 0
    for b in range(j_lo, j_hi + 1):
        ok = True
        for e in E:
            v = (e * b) % N
            if v < L or v > (n - 1) * L:
                ok = False
                break
        if ok:
            count += 1
    return count, j_hi - j_lo + 1 if j_hi >= j_lo else 0

def run_case(E, n, d):
    E = tuple(E)
    if len(set(E)) != len(E) or math.gcd(*E) != 1:
        return None
    x0, L = x0_full(E, n)
    jsafe, jsize = j_safe_count(E, n)
    phi_n = n - 1
    return (E, L, x0, phi_n, jsafe, jsize, x0 >= phi_n)

def build_cases():
    cases = []
    # n = 5
    n = 5
    units = [1,2,3,4]
    for d in units:
        R_non_pool = [u for u in units if u != d]
        for M_res in R_non_pool:
            E_non = tuple(u for u in R_non_pool if u != M_res)
            for k_div in [1,2]:
                for M in [M_res, M_res+n, M_res+2*n]:
                    E = tuple(list(E_non) + [k_div*n, M])
                    cases.append((E, n, d, f"n=5,d={d},E_non={E_non},k={k_div},M={M}"))
    # n = 7
    n = 7
    units = list(range(1,7))
    for d in units:
        R_non_pool = [u for u in units if u != d]
        for M_res in R_non_pool:
            E_non = tuple(u for u in R_non_pool if u != M_res)
            for k_div in [1]:
                for M in [M_res, M_res+n]:
                    E = tuple(list(E_non) + [k_div*n, M])
                    cases.append((E, n, d, f"n=7,d={d},E_non={E_non},k={k_div},M={M}"))
    # n = 11, A.8 non-canonical
    n = 11
    E_non_a8 = (1,2,3,4,5,6,8,40)
    for M in [10, 21, 32]:
        E = tuple(list(E_non_a8) + [n, M])
        cases.append((E, n, 9, f"n=11 A.8 speed40,d=9,M={M}"))
    return cases

def main():
    cases = build_cases()
    total = 0
    violations = []
    j_misses = 0  # late-window J missed it but x_0 still OK
    for entry in cases:
        E, n, d, name = entry
        r = run_case(E, n, d)
        if r is None:
            continue
        total += 1
        _, L, x0, phi_n, jsafe, jsize, ok = r
        if not ok:
            violations.append((name, E, L, x0, phi_n, jsafe, jsize))
        elif jsafe < phi_n:
            j_misses += 1

    print(f"Total valid cases: {total}")
    print(f"x_0 >= phi(n): {total - len(violations)}")
    print(f"x_0 < phi(n) (GENUINE violations): {len(violations)}")
    print(f"J-window missed but x_0 still >= phi(n): {j_misses}")
    if violations:
        print("\nVIOLATIONS:")
        for v in violations:
            print(f"  {v}")
    return 0 if not violations else 1

if __name__ == "__main__":
    raise SystemExit(main())
