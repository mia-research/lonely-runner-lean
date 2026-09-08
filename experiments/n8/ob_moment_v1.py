r"""
ob_moment_v1 -- the COLLISION-MOMENT bound.

  nu_rho = a_rho XOR mu_rho  (Klein coordinate; see ob_core_v1).
  C(x)   = #{ (i,j), i<j : nu_i = nu_j }   in {0,1,2,3,6}.
  O      = { C = 0 }.

  POINTWISE INEQUALITY   1[C=0] <= (C-2)(C-3)/6   for every C in {0,1,2,3,6}:
       C=0 -> 6/6 = 1 (equality) ; C=1 -> 2/6 ; C=2 -> 0 ; C=3 -> 0 ; C=6 -> 12/6.
  Hence  o <= ( E C^2 - 5 E C + 6 ) / 6 =: B.

  Under equidistribution E C = 3/2, E C^2 = 27/8, so B = 5/16 < 1/3 with margin 1/48.
  The LP that produced (C-2)(C-3)/6 is re-solved here from scratch (all quadratics
  a - b c + d c^2 >= 1[c=0] on {0,1,2,3,6}) so the choice is certified optimal.

Everything exact.  Cells evaluated at their ENTRY point; boundary audit reported.
"""
import sys, itertools
from fractions import Fraction as F
from functools import reduce
from math import gcd, lcm
from ob_core_v1 import (MUV, primitive_tuples, relations, _cellpts_t, audit_torus)

PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def sweep(speeds):
    """one exact pass over the theta-grid; returns (o, EC, EC2, dist) with dist the
    exact measure of each value of C."""
    D, p = _cellpts_t(speeds)
    dist = {}
    for i in range(len(p) - 1):
        a = p[i]
        nu = tuple((((4 * e * a) // D) % 4) ^ m for e, m in zip(speeds, MUV))
        C = sum(1 for u, v in PAIRS if nu[u] == nu[v])
        dist[C] = dist.get(C, 0) + p[i + 1] - a
    o = F(dist.get(0, 0), D)
    EC = sum(F(c * w, D) for c, w in dist.items())
    EC2 = sum(F(c * c * w, D) for c, w in dist.items())
    return o, EC, EC2, {c: F(w, D) for c, w in dist.items()}


def bound(EC, EC2):
    return (EC2 - 5 * EC + 6) / 6


def lp_certify():
    """exhaust the vertices of the LP  min  a - b*EC + d*EC2  s.t. a=1,
    a - b c + d c^2 >= 0 for c in {1,2,3,6}, at the equidistributed moments."""
    EC, EC2 = F(3, 2), F(27, 8)
    Cs = [1, 2, 3, 6]
    best = None
    for c1, c2 in itertools.combinations(Cs, 2):
        # solve 1 - b c1 + d c1^2 = 0, 1 - b c2 + d c2^2 = 0
        det = (-c1) * (c2 * c2) - (-c2) * (c1 * c1)
        if det == 0:
            continue
        b = F(-(c2 * c2) + (c1 * c1), det)
        d = F(-(-c1) + (-c2), det)
        if all(1 - b * c + d * c * c >= 0 for c in Cs):
            val = 1 - b * EC + d * EC2
            if best is None or val < best[0]:
                best = (val, b, d, (c1, c2))
    return best


if __name__ == "__main__":
    val, b, d, act = lp_certify()
    print("LP certificate for the pointwise majorant  1 - b C + d C^2 >= 1[C=0]:")
    print(f"   optimal b = {b}, d = {d}   (active at C = {act})")
    print(f"   equidistributed value of the bound = {val} = {float(val):.6f}"
          f"   (1/3 = {float(F(1,3)):.6f}, margin {F(1,3)-val})")
    print(f"   i.e. the majorant is (C-2)(C-3)/6 : b=5/6 {b==F(5,6)}, d=1/6 {d==F(1,6)}")

    QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    THIRD = F(1, 3)
    print(f"\nsweep over primitive unit 4-tuples, q <= {QMAX}")
    n = ncert = 0
    fails = []
    for e in primitive_tuples(QMAX):
        n += 1
        o, EC, EC2, dist = sweep(e)
        B = bound(EC, EC2)
        assert o <= B, (e, o, B)
        if B <= THIRD:
            ncert += 1
        else:
            fails.append((B, o, e, EC, EC2))
    print(f"   tuples: {n};  bound B <= 1/3 (so (H'') certified): {ncert}"
          f"   ({100.0*ncert/n:.2f}%)")
    print(f"   B > 1/3, bound inconclusive: {len(fails)}")
    fails.sort(reverse=True)
    print(f"   {'B':>12} {'o':>12} {'tuple':>20} {'E C':>10} {'E C^2':>10}  rel")
    for B, o, e, EC, EC2 in fails[:25]:
        print(f"   {float(B):>12.5f} {float(o):>12.5f} {str(e):>20} "
              f"{float(EC):>10.5f} {float(EC2):>10.5f}  {relations(e)}")
