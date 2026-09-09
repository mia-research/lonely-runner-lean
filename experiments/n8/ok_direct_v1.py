r"""
ok_direct_v1 -- exact o, computed independently of ob_core, plus the HI-BIT relaxation.

o_x(e)      : x in [0,1),   a_rho = floor(e_rho x / 2) mod 4          (the real object)
o_torus(e)  : theta in [0,1), a_rho = floor(4*frac(e_rho theta))      (the limit object)

BSM discipline: every breakpoint of every a_rho is an integer multiple of 1/D, so a_rho is
constant on each cell [j/D,(j+1)/D) and ENTRY value = EXIT value.  Asserted, not assumed.

HI-BIT RELAXATION.  a = (alpha,beta) in (Z/2)^2, mu = (0,1,2,3) -> mu^hi = (0,0,1,1).
nu injective ==> nu^hi has two 0s and two 1s ==> alpha_1 + alpha_3 = alpha_5 + alpha_7.
So  o <= H := |{alpha_1+alpha_3 = alpha_5+alpha_7}|.  Generic H = 3/8.
"""
from fractions import Fraction as F
from math import lcm
from functools import reduce
import itertools, sys

MUV = (0, 1, 2, 3)

def _D_and_check_x(e):
    L = reduce(lcm, e)
    # a_rho = floor(e_rho x / 2) mod 4 : breakpoints at x = 2k/e_rho -> multiples of 1/L? 
    # 2/e_rho = (2L/e_rho)/L, and L/e_rho is an integer, so yes: multiples of 1/L.
    for x in e:
        assert L % x == 0
    return L

def o_x(e, want_hi=False):
    D = _D_and_check_x(e)
    tot = 0; hi = 0
    for j in range(D):
        a = [((e[i]*j)//D // 2) % 4 for i in range(4)]
        if want_hi:
            al = [v >> 1 for v in a]
            if al[0]+al[1] == al[2]+al[3]:
                hi += 1
        nu = [a[i] ^ MUV[i] for i in range(4)]
        if len(set(nu)) == 4:
            tot += 1
    return (F(tot, D), F(hi, D)) if want_hi else F(tot, D)

def o_torus(e, want_hi=False):
    L = reduce(lcm, e)
    D = 4*L
    for x in e:
        assert D % (4*x) == 0
    tot = 0; hi = 0
    for j in range(D):
        a = [((e[i]*j)//L) % 4 for i in range(4)]
        if want_hi:
            al = [v >> 1 for v in a]
            if al[0]+al[1] == al[2]+al[3]:
                hi += 1
        nu = [a[i] ^ MUV[i] for i in range(4)]
        if len(set(nu)) == 4:
            tot += 1
    return (F(tot, D), F(hi, D)) if want_hi else F(tot, D)

# ---- boundary audit (requirement (i)): entry value == exit value on every cell -------
def audit(e):
    L = reduce(lcm, e); D = 4*L
    bad = 0
    for j in range(min(D, 4000)):
        for i in range(4):
            lo = ((e[i]*j)//L) % 4
            # exit = limit from the left of the next breakpoint: evaluate at (j+1)*D^- 
            hiv = ((e[i]*(j+1)-1)//L) % 4 if e[i]*(j+1) > 0 else lo
            if lo != hiv:
                bad += 1
    return bad

if __name__ == "__main__":
    from collections import defaultdict
    LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    print(f"# sweep: primitive unit 4-tuples (e1,e3,e5,e7), e_rho = rho mod 8, e_rho <= {LIM}")
    print("# audit on the first tuple:", audit((1,3,5,7)), "cells with entry != exit")
    from math import gcd
    res = []
    for e1 in range(1, LIM+1, 8):
        for e3 in range(3, LIM+1, 8):
            for e5 in range(5, LIM+1, 8):
                for e7 in range(7, LIM+1, 8):
                    e = (e1,e3,e5,e7)
                    if reduce(gcd, e) != 1: continue
                    ox, hx = o_x(e, True)
                    ot, ht = o_torus(e, True)
                    res.append((ox, ot, hx, ht, e))
    res.sort(key=lambda r: -r[0])
    print(f"\n{len(res)} primitive tuples.  TOP 12 by o_x:")
    print(f"{'e':22} {'o_x':>12} {'~':>8} {'o_torus':>12} {'~':>8} {'H_x':>10} {'H_t':>10}")
    for ox, ot, hx, ht, e in res[:12]:
        print(f"{str(e):22} {str(ox):>12} {float(ox):8.5f} {str(ot):>12} {float(ot):8.5f} {str(hx):>10} {str(ht):>10}")
    print(f"\n  o_x == o_torus on all {len(res)}? ", all(r[0]==r[1] for r in res))
    print(f"  H_x == H_torus on all?            ", all(r[2]==r[3] for r in res))
    over = [r for r in res if r[0] > F(1,3)]
    print(f"\n  tuples with o_x > 1/3: {len(over)}")
    for ox, ot, hx, ht, e in over:
        print(f"    {str(e):22} o={str(ox):>10} = {float(ox):.5f}")
    le = [r for r in res if r[0] <= F(1,3)]
    if le:
        print(f"  max o_x among the rest: {le[0][0]} = {float(le[0][0]):.5f}  at {le[0][4]}")
    print(f"\n  max H_x over all tuples: {max(r[2] for r in res)} = {float(max(r[2] for r in res)):.5f}")
    print(f"  min H_x over all tuples: {min(r[2] for r in res)} = {float(min(r[2] for r in res)):.5f}")
    # is o <= H everywhere (sanity on the implication)?
    print("  o_x <= H_x everywhere?", all(r[0] <= r[2] for r in res))
