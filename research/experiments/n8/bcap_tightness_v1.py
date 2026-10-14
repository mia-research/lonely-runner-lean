"""Exact max-min gap (tightness) of a speed set, and the boundary-witness
diagnosis for BCAP counterexamples.  Fractions only, no floats.
Run: python3 bcap_tightness_v1.py
"""
from fractions import Fraction as F
from bcap_attack_v1 import *

def norm(x):
    """||x|| = distance to nearest integer, exact."""
    r = x - (x.numerator // x.denominator)
    return min(r, 1 - r)

def maxmin_gap(T):
    """max_t min_{u in T} ||u t||, exact.
    f(t)=min ||ut|| is piecewise linear; every local max is a breakpoint
    k/(2u) or a crossing c/(2(u+/-v)).  Evaluate all such rationals."""
    dens = set()
    for u in T:
        dens.add(2*u)
    for u in T:
        for v in T:
            if u+v: dens.add(2*(u+v))
            if u!=v: dens.add(2*abs(u-v))
    best = F(0); arg = []
    for d in sorted(dens):
        for k in range(0, d+1):
            t = F(k, d)
            val = min(norm(u*t) for u in T)
            if val > best:
                best, arg = val, [t]
            elif val == best and t not in arg:
                arg.append(t)
    return best, sorted(arg)

def diagnose(n, SG, SA, p):
    T = sorted(set(SG) | set(p*v for v in SA))
    g, args = maxmin_gap(T)
    tight = (g == F(1, n))
    # witnesses achieving >= 1/n
    wit = [t for t in args if g >= F(1,n)]
    return T, g, tight, wit[:4]

CASES = [
 (3,[1],[1],2), (3,[3],[3],2), (3,[5],[5],2),
 (4,[1,2],[1],3), (4,[1,3],[1],2), (4,[2,4],[2],3),
 (5,[1,3],[1,2],2), (5,[1,2,4],[1],3), (5,[1,3,4],[1],7),
 (6,[1,3,5],[1,2],2), (6,[1,4,5],[1,3],3), (6,[1,2,3,4],[1],5),
 (8,[1,2,4,5,7],[1,2],3), (8,[1,2,4,5,7],[1,4],3),
 (8,[1,2,3,4,5,6],[1],7), (8,[1,2,3,4,6,7],[1],5),
]
if __name__ == "__main__":
    print(f"{'n':>2} {'S_G':<18}{'S_A':<8}{'p':>3}  {'T':<24}{'maxmin gap':>12} {'=1/n?':>6}  witnesses")
    for n,SG,SA,p in CASES:
        T,g,tight,wit = diagnose(n,SG,SA,p)
        print(f"{n:>2} {str(SG):<18}{str(SA):<8}{p:>3}  {str(T):<24}{str(g):>12} {str(tight):>6}  {[str(w) for w in wit]}")
    print()
    # boundary-witness diagnosis for the headline n=8 case
    n,SG,SA,p = 8,[1,2,3,4,5,6],[1],7
    t = F(1,8)
    print("n=8 headline case, candidate witness t = 1/8:")
    print("  ||u t|| for u in S_G :", [str(norm(u*t)) for u in SG])
    print("  ||v (p t)|| for v in S_A, {pt} =", str(F(p*t.numerator, t.denominator) - 0),
          "->", [str(norm(v*p*t)) for v in SA])
    print("  all >= 1/8 ?", all(norm(u*t) >= F(1,8) for u in SG) and all(norm(v*p*t) >= F(1,8) for v in SA))
    LG = lcm(SG)
    print(f"  t sits at grid index m = {t * n * LG} of the {n*LG} G-cells: a CELL ENDPOINT, not an interior point.")
