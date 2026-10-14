r"""
ok_umax_v1 -- the shape-free quantity.  u(E_non) = |{x : the non-divisible runners block
every residue of Z/8}|.  A witness exists whenever  u(E_non) + |union B_m| < 1.

Since |E_non| = 7 - |E_div|, the thresholds are
   |E_div| = 1  ->  |E_non| = 6,  need u < 3/4      (|B_m| = 1/4 exactly)
   |E_div| = 2  ->  |E_non| = 5,  need u < 1/2      (B-lemma: |B1 u B2| < 1/2)
   |E_div| = 3  ->  |E_non| = 4,  need u < 1 - |B1 u B2 u B3|

Block sizes, by g = gcd(e,8)  [verified separately]:
   g=1 (unit)  : exactly 2 residues, {-t*rho, -(t+1)*rho} -- one odd, one even
   g=2 (rho 2,6): exactly 2 residues, {r0, r0+4} -- SAME parity, which parity depends on t
   g=4 (rho 4) : 4 residues (all evens if t mod 8 in {0,7}, all odds if in {3,4}), else 0
So covering Z/8 needs the odd half and the even half covered separately.

u is a DILATION INVARIANT (u(lambda E) = u(E)), so only primitive E_non matter.
Exact rationals; cells are the union of all breakpoints j/e, so ENTRY value = value
throughout; audit() re-checks entry vs exit.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd
import sys

def bad(e,t): return frozenset(r for r in range(8) if (e*r+t)%8 in (0,7))
def cells(S):
    pts={F(0),F(1)}
    for e in S:
        for j in range(1,e+1):
            q=F(j,e)
            if 0<q<1: pts.add(q)
    p=sorted(pts); return list(zip(p,p[1:]))
def fl(e,a): v=e*a; return v.numerator//v.denominator

def u_of(E):
    tot=F(0)
    for a,b in cells(E):
        cov=set()
        for e in E: cov|=bad(e,fl(e,a))
        if len(cov)==8: tot+=b-a
    return tot

def audit(E):
    bad_ct=0
    for a,b in cells(E):
        ex=a+(b-a)*F(999999,1000000)
        for e in E:
            if fl(e,a)!=fl(e,ex): bad_ct+=1
    return bad_ct

if __name__=="__main__":
    N=int(sys.argv[1]) if len(sys.argv)>1 else 20
    pool=[e for e in range(1,N+1) if e%8!=0]
    print(f"# E_non drawn from [1..{N}] minus multiples of 8 -> {len(pool)} speeds")
    print(f"# boundary audit on [1,3,5,7,4]: {audit([1,3,5,7,4])} entry/exit mismatches\n")
    print(f"{'k':>2} {'#primitive':>11} {'max u':>12} {'~':>9}  {'argmax':28} {'threshold':>12} {'ok?'}")
    NEED={6:F(3,4), 5:F(1,2), 4:None}
    for k in (4,5,6):
        best=None; n=0
        for E in combinations(pool,k):
            if reduce(gcd,E)!=1: continue
            n+=1
            uu=u_of(list(E))
            if best is None or uu>best[0]: best=(uu,E)
        thr=NEED[k]
        ok = "" if thr is None else ("YES" if best[0]<thr else "NO  <-- fails")
        print(f"{k:>2} {n:>11} {str(best[0]):>12} {float(best[0]):9.6f}  {str(best[1]):28} "
              f"{str(thr) if thr else '-':>12} {ok}")
    print("\ntop 6 by u at k = 5 (the |E_div| = 2 case, threshold 1/2):")
    rows=[]
    for E in combinations(pool,5):
        if reduce(gcd,E)!=1: continue
        rows.append((u_of(list(E)),E))
    rows.sort(key=lambda r:-r[0])
    for uu,E in rows[:6]:
        print(f"    {str(E):28} u = {str(uu):>10} = {float(uu):.6f}"
              f"{'   >= 1/2' if uu>=F(1,2) else ''}")
