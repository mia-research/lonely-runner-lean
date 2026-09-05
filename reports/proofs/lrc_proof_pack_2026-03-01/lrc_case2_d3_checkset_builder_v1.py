#!/usr/bin/env python3
"""
Build D.3 finite check-set T(F) for one-parameter Case-2 templates.

Given:
  n, L0, a_F, b_F

Computes:
  R(F) = n*L0
  M0(F) = max(1, ceil(((n-1)-b_F)/a_F))
  T(F)  = {1 <= M < M0(F) : gcd(M, nL0)=1}

Outputs:
  - stdout summary
  - optional CSV rows for T(F)
"""

import argparse
import csv
import math
from fractions import Fraction
from math import gcd


def parse_fraction(x: str) -> Fraction:
    """Parse numeric input as exact Fraction.
    Accepts forms like '3/7', '1.25', '5'.
    """
    return Fraction(x)


def build_checkset(n: int, L0: int, a: Fraction, b: Fraction):
    if a <= 0:
        raise ValueError("a_F must be positive")

    rhs = Fraction(n - 1) - b
    if rhs <= 0:
        M0 = 1
    else:
        M0 = math.ceil(rhs / a)
        if M0 < 1:
            M0 = 1

    R = n * L0
    T = [m for m in range(1, M0) if gcd(m, R) == 1]
    return R, M0, T


def main():
    ap = argparse.ArgumentParser(description="Build D.3 finite check set T(F)")
    ap.add_argument("--n", type=int, required=True, help="prime n (runner count frame)")
    ap.add_argument("--L0", type=int, required=True, help="family base multiplier (L=L0*M)")
    ap.add_argument("--a", type=str, required=True, help="slope a_F (fraction string, e.g. 37/22)")
    ap.add_argument("--b", type=str, required=True, help="intercept b_F (fraction string)")
    ap.add_argument("--tag", type=str, default="family", help="family tag for CSV")
    ap.add_argument("--csv", type=str, default="", help="optional output CSV path")
    args = ap.parse_args()

    a = parse_fraction(args.a)
    b = parse_fraction(args.b)

    R, M0, T = build_checkset(args.n, args.L0, a, b)

    print("D.3 CHECKSET SUMMARY")
    print(f"tag={args.tag}")
    print(f"n={args.n}, L0={args.L0}")
    print(f"a_F={a}, b_F={b}")
    print(f"R(F)=n*L0={R}")
    print(f"M0(F)={M0}")
    print(f"|T(F)|={len(T)}")
    if len(T) <= 50:
        print(f"T(F)={T}")
    else:
        print(f"T(F) head={T[:25]}")
        print(f"T(F) tail={T[-25:]}")

    if args.csv:
        with open(args.csv, "w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow(["tag", "n", "L0", "R", "M0", "M", "check"])
            for m in T:
                w.writerow([args.tag, args.n, args.L0, R, M0, m, 1])
        print(f"wrote: {args.csv}")


if __name__ == "__main__":
    main()
