#!/usr/bin/env python3
"""case_63 branch-8 fallback, nu(e45)=1: 7-pin decide verification.

Setting (h=m, ratio-3, T34 = q(e34) in {3,4,5}, nu(e45)=1 exactly):
one Lambda_1 knob k2 sets pin p = q(7*w*d3) AND shifts e_val = q(w*e45)
linearly: e_val = e0 + p*rho (rho != 0 fixed by the config).

Doubling carry eps1 of w*d3 at level m:
  p in {0,1,2} -> eps1 = 0
  p in {4,5,6} -> eps1 = 1
  p = 3        -> eps1 unknown in {0,1}  (case-split at proof time)

Placement after Lambda_m base shift to Atar:
  A1 arcs : {Atar, Atar+1, Atar+3}
  d4 arc  : 2*Atar + eps1 - T34
  d5 arc  : 4*Atar + 2*eps1 - 2*T34 - e_val + cc,  cc in {0,1,6} (uncontrolled
            qz_2xsuby carry, case-split at proof time AFTER k2 fixed)

CLAIM (fallback_63_l1): for all T34 in {3,4,5}, e0 in Z7, rho in Z7\{0}:
  exists p such that for ALL eps1 compatible with p, for ALL cc in {0,1,6},
  exists Atar with all five arcs avoiding {0,6}.
"""

Z = list(range(7))
BAD = {0, 6}


def ok(x):
    return x % 7 not in BAD


def placement_ok(Atar, T34, eps1, e_val, cc):
    a1 = [Atar, Atar + 1, Atar + 3]
    d4 = 2 * Atar + eps1 - T34
    d5 = 4 * Atar + 2 * eps1 - 2 * T34 - e_val + cc
    return all(ok(x) for x in a1 + [d4, d5])


def compatible_eps1(p):
    if p in (0, 1, 2):
        return [0]
    if p in (4, 5, 6):
        return [1]
    return [0, 1]  # p == 3


def pin_wins(p, T34, e0, rho):
    e_val = (e0 + p * rho) % 7
    for eps1 in compatible_eps1(p):
        for cc in (0, 1, 6):
            if not any(placement_ok(A, T34, eps1, e_val, cc) for A in Z):
                return False
    return True


def main():
    fails = []
    total = 0
    for T34 in (3, 4, 5):
        for e0 in Z:
            for rho in range(1, 7):
                total += 1
                if not any(pin_wins(p, T34, e0, rho) for p in Z):
                    fails.append((T34, e0, rho))
    print(f"configs checked: {total}")
    print(f"failures: {len(fails)}")
    if fails:
        for f in fails:
            print("  FAIL (T34,e0,rho) =", f)
    else:
        print("ALL PASS — fallback_63_l1 decide is TRUE.")

    # Comparison: even-pin-only strategy (the old route) — expected to fail some.
    fails_even = 0
    for T34 in (3, 4, 5):
        for e0 in Z:
            for rho in range(1, 7):
                if not any(pin_wins(p, T34, e0, rho) for p in (0, 2, 4, 6)):
                    fails_even += 1
    print(f"[control] even-pin-only failures: {fails_even}/126")


if __name__ == "__main__":
    main()
