r"""
ok_exact_sc_v1 -- evaluate |S^c| EXACTLY, instead of through the two relaxations that
produce the (H'') threshold o <= 1/3.

Exact identity (hp_apriori_v1 (*)), for the rho0 = 4 fibre with divisible speed m = 4 mod 8:
    |S^c| = |A_none n U| + |A_even n O| + |A_odd n V|
  A_even = {t_m = 0,7}  (m blocks the EVEN residues)
  A_odd  = {t_m = 3,4}  (m blocks the ODD residues)
  A_none = {t_m = 1,2,5,6}
  O = units block all odds;  V = units block all evens;  U = O n V = units block everything.
The leaf closes for this (E,m) iff |S^c| < 1/2.

(H'') asks o <= 1/3.  The exact question is whether |S^c| < 1/2.  These are NOT the same:
the chain to 1/3 goes through |S^c| <= o - beta + min(1/4,o), two inequalities deep.

BSM: breakpoints of floor(e*x) are the multiples of 1/e; the cell list is their union, so
no breakpoint is interior and ENTRY value = value throughout.  audit() rechecks.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
import sys

FULL = frozenset(range(8)); ODD = frozenset({1,3,5,7}); EVEN = frozenset({0,2,4,6})

def cells(S):
    pts = {F(0), F(1)}
    for e in S:
        for j in range(1, e+1):
            q = F(j, e)
            if 0 < q < 1: pts.add(q)
    p = sorted(pts)
    return list(zip(p, p[1:]))

def fl(e, a):
    v = e*a; return v.numerator // v.denominator

def bad(e, t):
    return frozenset(r for r in range(8) if (e*r + t) % 8 in (0, 7))

def audit(S):
    """entry value == exit value for floor(e*x) on every cell"""
    bad_ct = 0
    for a, b in cells(S):
        ex = a + (b-a)*F(999999, 1000000)
        for e in S:
            if fl(e, a) != fl(e, ex): bad_ct += 1
    return bad_ct

def analyse(U4, m):
    """returns (o, v, u, alpha, beta, gamma_U, Sc) exactly"""
    S = list(U4) + [m]
    o = v = u = F(0); alpha = beta = F(0); Sc = F(0); AnU = F(0)
    for a, b in cells(S):
        w = b - a
        cov = set()
        for e in U4: cov |= bad(e, fl(e, a))
        inO = ODD <= cov; inV = EVEN <= cov; inU = inO and inV
        if inO: o += w
        if inV: v += w
        if inU: u += w
        t = fl(m, a) % 8
        if t in (0, 7):                       # A_even
            if inO: alpha += w; Sc += w
        elif t in (3, 4):                     # A_odd
            if inO: beta += w
            if inV: Sc += w
        else:                                 # A_none
            if inU: AnU += w; Sc += w
    return o, v, u, alpha, beta, AnU, Sc

if __name__ == "__main__":
    MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    print("# audit (entry vs exit) on [1,3,5,7,4]:", audit([1,3,5,7,4]), "mismatches\n")
    EXC = [(1,3,5,7), (1,11,5,7)]
    for U4 in EXC:
        o0 = None; worst = None; fails = []
        print(f"=== EXCEPTIONAL TUPLE {U4} (o > 1/3, so (H'') does NOT cover it) ===")
        for m in range(4, MMAX+1, 8):
            o, v, u, al, be, AnU, Sc = analyse(U4, m)
            o0 = o
            if worst is None or Sc > worst[0]: worst = (Sc, m, o, v, u, al, be, AnU)
            if Sc >= F(1,2): fails.append((m, Sc))
        Sc, m, o, v, u, al, be, AnU = worst
        print(f"  o = {o} = {float(o):.6f}   (> 1/3 = {float(o) > 1/3})")
        print(f"  over m = 4,12,...,{MMAX}:  max |S^c| = {Sc} = {float(Sc):.6f}  at m = {m}")
        print(f"     at that m:  v={v} u={u} alpha={al} beta={be} |A_none n U|={AnU}")
        print(f"  m with |S^c| >= 1/2 : {len(fails)}  {[f[0] for f in fails][:12]}")
        print()
