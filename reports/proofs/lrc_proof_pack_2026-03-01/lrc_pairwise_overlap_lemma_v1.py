#!/usr/bin/env python3
from __future__ import annotations

from fractions import Fraction
import math
import random
from itertools import combinations


def dangerous_indicator(e: int, n: int, N: int, k: int) -> int:
    v = (e * Fraction(k, N)) % 1
    return int(not (Fraction(1, n) <= v <= Fraction(n - 1, n)))


def brute_single_size(e: int, n: int, L: int) -> int:
    N = n * L
    return sum(dangerous_indicator(e, n, N, k) for k in range(N))


def brute_pair_overlap(a: int, b: int, n: int, L: int) -> int:
    N = n * L
    out = 0
    for k in range(N):
        if dangerous_indicator(a, n, N, k) and dangerous_indicator(b, n, N, k):
            out += 1
    return out


def count_residue_in_interval(lo: int, hi: int, r: int, d: int) -> int:
    if lo > hi:
        return 0
    x = lo + ((r - lo) % d)
    if x > hi:
        return 0
    return 1 + (hi - x) // d


def c_count(e: int, n: int, L: int, r: int, d: int) -> int:
    # m_e = nL/e, p_e = L/e.
    p = L // e
    m = n * p
    # R_e = [0,p-1] U [m-p+1,m-1]
    low = count_residue_in_interval(0, p - 1, r, d)
    high = count_residue_in_interval(m - p + 1, m - 1, r, d)
    return low + high


def formula_pair_overlap(a: int, b: int, n: int, L: int) -> int:
    # Exact CRT residue formula on Z_N, N=nL.
    ma = n * (L // a)
    mb = n * (L // b)
    d = math.gcd(ma, mb)
    g = math.gcd(a, b)

    total = 0
    for r in range(d):
        total += c_count(a, n, L, r, d) * c_count(b, n, L, r, d)
    return g * total


def verify(samples: int = 300) -> None:
    # Exact single-size law
    for n in range(3, 9):
        for a in range(1, 11):
            for b in range(1, 11):
                L = math.lcm(a, b)
                s = brute_single_size(a, n, L)
                assert s == 2 * L - a, (n, a, b, L, s, 2 * L - a)

    # Pairwise formula checks
    random.seed(0)
    for _ in range(samples):
        n = random.randint(3, 10)
        a = random.randint(1, 12)
        b = random.randint(1, 12)
        c = random.randint(1, 12)
        L = math.lcm(a, b, c)
        br = brute_pair_overlap(a, b, n, L)
        fm = formula_pair_overlap(a, b, n, L)
        assert br == fm, (n, a, b, L, br, fm)


def demo() -> None:
    cases = [
        (4, [1, 2, 3]),
        (5, [1, 2, 3, 4]),
        (5, [1, 3, 4, 7]),
        (6, [1, 2, 3, 4, 5]),
    ]
    for n, e_list in cases:
        L = math.lcm(*e_list)
        print(f"n={n}, e_list={e_list}, L={L}, N={n*L}")
        for e in e_list:
            s = brute_single_size(e, n, L)
            print(f"  |D_{e}| = {s} = 2L-e={2*L-e}")
        for a, b in combinations(e_list, 2):
            br = brute_pair_overlap(a, b, n, L)
            fm = formula_pair_overlap(a, b, n, L)
            print(f"  |D_{a}∩D_{b}| = {br} (formula {fm})")
        print()


if __name__ == "__main__":
    verify(300)
    print("VERIFIED: single-size and pairwise overlap formulas")
    demo()
