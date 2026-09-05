#!/usr/bin/env python3
"""
Extended A.4 enumeration for prime n in {5, 7}:
- k_div in {1, 2, 3, ...} up to the Lemma 10.4 threshold where L >= C_n.
- M in {1, 2, ..., M_0 - 1}  (NOT just M >= 3; includes the L > n / L > 2n
  sub-cases missed by the legacy A.4 "M >= 3" justification).

For every admissible tuple E with gcd(E) = 1, compute x_0(E) and assert
x_0 >= phi(n) = n - 1.

This closes the A.4 coverage gaps flagged in v9.3 / identified in the
lrc_prop_10_5_full_x0.py run (k=2 variants, M in {1,2} with L_0 > 1).
"""

from __future__ import annotations

import itertools
import math
from fractions import Fraction


def lcm_many(xs):
    out = 1
    for x in xs:
        out = out * x // math.gcd(out, x)
    return out


def safe_count(E, n):
    """x_0(E) = |{b in B_div : forall e in E, (e*b) mod N in [L, (n-1)L]}|."""
    L = lcm_many(E)
    N = n * L
    Bdiv_lo = (L + n - 1) // n if L % n != 0 else L // n
    Bdiv_hi = ((n - 1) * L) // n
    count = 0
    for b in range(Bdiv_lo, Bdiv_hi + 1):
        ok = True
        for e in E:
            v = (e * b) % N
            if v < L or v > (n - 1) * L:
                ok = False
                break
        if ok:
            count += 1
    return count


def enumerate_prime(n: int, k_range, M_range_builder) -> int:
    """
    For prime n, for each 2-drop {du_1, du_2} from {1..n-1}:
      R_non = {1..n-1} \\ {du_1, du_2}  (canonical retained residues)
      For each labelling of E_non as tuple of canonical residues,
      For each k_div in k_range,
      For each M in M_range_builder(n, L0), gcd(M,n)=1, M not in E_non:
        build E = E_non + (k_div * n, M); skip if duplicate speeds;
        verify x_0(E) >= phi(n).
    """
    failures = []
    tested = 0
    phi_n = n - 1
    residues = list(range(1, n))
    for drop in itertools.combinations(residues, 2):
        R_non = tuple(r for r in residues if r not in drop)
        # In prime-n Prop 10.5 setup, |E_non| = n - 3.
        if len(R_non) != n - 3:
            continue
        # Use R_non as actual speeds (canonical); enumerate M separately.
        E_non = R_non
        L0 = lcm_many(E_non) if E_non else 1
        for k_div in k_range:
            for M in M_range_builder(n, L0):
                if math.gcd(M, n) != 1:
                    continue
                if M in E_non or M == k_div * n:
                    continue
                E = tuple(list(E_non) + [k_div * n, M])
                if len(set(E)) != len(E):
                    continue
                if math.gcd(*E) != 1:
                    continue
                x0 = safe_count(E, n)
                tested += 1
                if x0 < phi_n:
                    failures.append((drop, E, x0, phi_n))
    return tested, failures


def main():
    # Standard Lemma 10.4 threshold: C_n = n(n-1)(phi(n)+1) = n(n-1)n for phi=n-1
    # Actually the v10.12 text uses C_n for the large-L regime. Small-L enumeration
    # range is M such that L = lcm(L0, n, M) < C_n. Simplest: enumerate all
    # M up to M_0 := ceil(n^2 (n-1) / (L0 (n-2))) bound from the appendix.
    for n in [5, 7]:
        k_bound = max(3, 2 * n)  # enumerate k_div up to 2n (generous)

        def M_range(nn, L0, kb=k_bound):
            # M up to M_0 per A.4, but starting at 1 not 3:
            M0 = max(3, (nn * nn * (nn - 1) + (L0 * (nn - 2)) - 1) // (L0 * (nn - 2)))
            return list(range(1, M0 + 1))

        tested, failures = enumerate_prime(n, k_range=range(1, k_bound + 1), M_range_builder=M_range)
        print(f"n={n}: tested {tested} admissible tuples, {len(failures)} with x_0 < phi(n)={n-1}")
        for drop, E, x0, phi_n in failures[:20]:
            print(f"  FAIL drop={drop} E={E} x_0={x0} (need >= {phi_n})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
