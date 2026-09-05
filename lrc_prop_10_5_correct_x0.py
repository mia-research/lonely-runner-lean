#!/usr/bin/env python3
"""
CORRECT x_0 count per v10.12 line 56:
  x_0(E) = #{k in {1, ..., N-1} : (e_i * k mod N) in [L, (n-1)L] for all e_i in E}
where N = n * L, L = lcm(E).

Re-check the 7 'failing' n=5 cases from lrc_prop_10_5_full_x0.py under this
correct definition. Also check the 20 cases flagged by the first harness.
"""

from __future__ import annotations
import math

def lcm_many(xs):
    out = 1
    for x in xs:
        out = out * x // math.gcd(out, x)
    return out

def x0_correct(E, n):
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
    return count, L, N

CASES = [
    # (E, n, description)
    ((1, 2, 4, 5), 5, "d=3, E_non=(2,4), M=1, k=1  — was x_0=0 in old harness"),
    ((1, 2, 4, 10), 5, "d=3, E_non=(2,4), M=1, k=2"),
    ((1, 4, 5, 8), 5, "d=2, E_non=(1,4), M=8, k=1"),
    ((1, 4, 10, 8), 5, "d=2, E_non=(1,4), M=8, k=2"),
    ((1, 3, 5, 9), 5, "d=2, E_non=(1,3), M=9, k=1"),
    ((1, 3, 10, 9), 5, "d=2, E_non=(1,3), M=9, k=2"),
    ((2, 4, 10, 8), 5, "d=1, E_non=(2,4), M=8, k=2"),
]

def main():
    print(f"{'Case':<55} {'L':>6} {'N':>7} {'x_0':>8} {'phi(n)':>6} status")
    print("-" * 100)
    fails = 0
    for E, n, desc in CASES:
        x0, L, N = x0_correct(E, n)
        phi_n = n - 1
        status = "OK" if x0 >= phi_n else "VIOLATION"
        if x0 < phi_n:
            fails += 1
        print(f"{desc:<55} {L:>6} {N:>7} {x0:>8} {phi_n:>6} {status}")
    print("-" * 100)
    print(f"Cases tested: {len(CASES)}, violations: {fails}")
    return 1 if fails else 0

if __name__ == "__main__":
    raise SystemExit(main())
