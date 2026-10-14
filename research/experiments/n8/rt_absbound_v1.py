r"""
rt_absbound_v1 -- how much of Theorem 1's expansion is cancellation?

Theorem 1:   o = (1/256) SUM_w K(w) eps(w) I(w),  the w = 0 term being 3/32.
The obvious route to (H3u) is the triangle inequality:

    |o - 3/32|  <=  ABS := (1/256) SUM_{w != 0} |K(w)| |I(w)| .

This script computes ABS exactly, split by |supp w|, alongside the true deviation, on the
tuples that matter (the census maximisers and the tail maximisers).  If ABS is far larger
than |o - 3/32| the triangle inequality cannot prove (H3u) at any height that leaves a
feasible finite check, and a proof has to use cancellation.  Exact Fractions throughout.

usage:  python3 rt_absbound_v1.py
"""
import itertools
from fractions import Fraction as F
from math import gcd

from rt_char_v1 import K_table, eps, I_all, o_direct

TUPLES = [
    (1, 3, 5, 7), (1, 11, 5, 7), (17, 3, 5, 7), (1, 3, 13, 15), (1, 11, 13, 23),
    (1, 19, 5, 7), (25, 11, 77, 7), (9, 11, 13, 15), (41, 43, 13, 15),
    (49, 11, 29, 23), (241, 163, 205, 199),
]


def support(w):
    return tuple(i for i, x in enumerate(w) if x)


if __name__ == "__main__":
    K = K_table()
    print("ABS = (1/256) SUM_{w != 0} |K(w)| |I(w)|   vs   the true |o - 3/32|")
    print("A proof by triangle inequality needs ABS small; the gap is the cancellation.\n")
    print(f"{'e':>24} {'o':>10} {'|o-3/32|':>10} {'ABS':>10} "
          f"{'ABS2':>9} {'ABS3':>9} {'ABS4':>9} {'ABS/dev':>8}")
    for e in TUPLES:
        I = I_all(e)
        o = o_direct(e)
        parts = {2: F(0), 3: F(0), 4: F(0)}
        for w in I:
            if not any(w) or K[w] == 0:
                continue
            k = len(support(w))
            parts[k] += abs(K[w]) * abs(I[w])
        tot = sum(parts.values()) / 256
        dev = abs(o - F(3, 32))
        print(f"{str(e):>24} {float(o):>10.6f} {float(dev):>10.6f} {float(tot):>10.6f} "
              f"{float(parts[2]/256):>9.6f} {float(parts[3]/256):>9.6f} "
              f"{float(parts[4]/256):>9.6f} "
              f"{(float(tot/dev) if dev else float('inf')):>8.2f}")
    print("\nThe budget that a triangle-inequality proof of (H3u) would have to fit inside")
    print("is 1/12 = 0.083333, on top of a class limit of at most 1/4.")
    print("Corollary 3.1 gives, for the |supp| = 2 part alone at height cut R,")
    print("   (144/256) / min_pair(e_i e_j / gcd^2)   and every tail pair has")
    print("   e_i e_j / gcd^2 >= R + 1, so the crude pair bound is 9/(16(R+1)):")
    for R in (2, 3, 4, 7, 10, 20):
        print(f"     R = {R:>3}   pair bound 9/(16*{R+1}) = {float(F(9,16*(R+1))):.6f}"
              f"   finite-check speed box 3 sqrt3 R^3 = {3*(3**0.5)*R**3:8.1f}")
