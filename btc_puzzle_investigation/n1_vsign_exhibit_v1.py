#!/usr/bin/env python3
"""
n1_vsign_exhibit_v1.py -- exhibit the `v > 0` counterexamples with EXACT RATIONAL ENCLOSURES.

The COUNT is already exact (Descartes + total-reality self-certificate, n1_vsign_decide_v1.py).
This script produces the witness: an isolating interval with RATIONAL endpoints for each offending
root of Q_p, mapped through the exact affine map to an interval for v.  Every endpoint is a
Fraction; the decimal rendering at the end is display only and decides nothing.

  SIN (p = 3 mod 4):  v = -(e2 + 2p)/(4p)   -- decreasing in e2, so the interval flips
  COS (p = 1 mod 4):  v =  (e2 - 2p)/(4p)
"""
import sys
from fractions import Fraction
import sympy as sp

sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from n1_vsign_decide_v1 import decide

Y = sp.Symbol("Y")


def exhibit(p):
    r = decide(p, verbose=False)
    Q, thr, sin, d = r["Q"], r["thr"], r["sin"], r["d"]
    P = sp.Poly(list(reversed(Q)), Y)
    ivs = P.intervals()                       # exact rational isolating intervals
    offending = []
    for (a, b), mult in ivs:
        a, b = Fraction(int(a.p), int(a.q)), Fraction(int(b.p), int(b.q))
        if sin and b < thr:
            offending.append((a, b, mult))
        if (not sin) and a > thr:
            offending.append((a, b, mult))

    print(f"p = {p}   n = {r['n']}   d = {d}   {'SIN' if sin else 'COS'}   "
          f"exact count of classes with v > 0 : {r['count']}")
    assert sum(m for _, _, m in offending) == r["count"], \
        "isolation disagrees with the Descartes count"
    for a, b, mult in offending:
        # v = -(e2+2p)/(4p) for SIN : e2 in (a,b) -> v in ( -(b+2p)/4p , -(a+2p)/4p )
        if sin:
            vlo, vhi = Fraction(-(b + 2 * p), 4 * p), Fraction(-(a + 2 * p), 4 * p)
        else:
            vlo, vhi = Fraction(a - 2 * p, 4 * p), Fraction(b - 2 * p, 4 * p)
        assert vlo > 0, "enclosure does not certify v > 0"
        print(f"    e2 in [{a}, {b}]  (mult {mult})")
        print(f"    => v in [{vlo}, {vhi}]   both endpoints RATIONAL and > 0")
        print(f"       decimal (display only): v in [{float(vlo):.9f}, {float(vhi):.9f}]")
    if not offending:
        print("    (none -- v <= 0 at every class)")
    print()
    return r


if __name__ == "__main__":
    for p in [int(t) for t in sys.argv[1:]]:
        exhibit(p)
