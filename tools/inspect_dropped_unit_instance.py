from __future__ import annotations

import argparse
from math import gcd, lcm


def inv_mod(a: int, n: int) -> int:
    return pow(a, -1, n)


def bad_set(e: int, b: int, L: int, n: int) -> set[int]:
    t = (e * b) // L
    rho = e % n
    out: set[int] = set()
    for r in range(n):
        if (rho * r + t) % n == 0:
            out.add(r)
        if (rho * r + t + 1) % n == 0:
            out.add(r)
    return out


def coverage_union(E_non: list[int], b: int, L: int, n: int) -> set[int]:
    union: set[int] = set()
    for e in E_non:
        union |= bad_set(e, b, L, n)
    return union


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--d", type=int, required=True)
    parser.add_argument("--E", type=str, required=True, help="Comma-separated speeds")
    parser.add_argument("--window", type=int, default=8, help="Show this many b values from b0 onward")
    args = parser.parse_args()

    n = args.n
    d = args.d
    E = tuple(int(x) for x in args.E.split(","))
    L = 1
    for e in E:
        L = lcm(L, e)
    b0 = L // n
    upper_b = ((n - 1) * L) // n
    E_non = [e for e in E if e % n != 0]
    r_d = (-inv_mod(d, n)) % n

    print({"n": n, "E": E, "d": d, "r_d": r_d, "L": L, "b0": b0, "upper_b": upper_b})
    print("patchers at b0:")
    for e in E_non:
        if r_d not in bad_set(e, b0, L, n):
            continue
        rho = e % n
        q = e // n
        print(
            {
                "e": e,
                "q": q,
                "rho": rho,
                "unit": gcd(rho, n) == 1,
                "covers_via_qd": (rho - q * d) % n == 0,
                "covers_via_q1d": (rho - (q + 1) * d) % n == 0,
            }
        )

    first_safe = None
    for b in range(b0, upper_b + 1):
        union = coverage_union(E_non, b, L, n)
        if len(union) < n:
            first_safe = b
            print({"first_safe_b": b, "missing": sorted(set(range(n)) - union)})
            break
    if first_safe is None:
        print({"first_safe_b": None})
        return

    print("local window:")
    stop = min(first_safe + args.window, upper_b + 1)
    for b in range(max(b0, first_safe - args.window), stop):
        union = coverage_union(E_non, b, L, n)
        missing = sorted(set(range(n)) - union)
        resetters = [e for e in E_non if (e * b) % L == 0]
        print({"b": b, "missing": missing, "resetters": resetters})

    print("runner snapshots at first safe b:")
    for e in E_non:
        print(
            {
                "e": e,
                "rho": e % n,
                "floor": (e * first_safe) // L,
                "bad": sorted(bad_set(e, first_safe, L, n)),
                "reset": (e * first_safe) % L == 0,
            }
        )


if __name__ == "__main__":
    main()
