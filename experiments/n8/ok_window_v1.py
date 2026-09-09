r"""
ok_window_v1 -- does the Slack Lemma's WINDOW actually contain a witness?

Slack Lemma hypothesis: R_non misses both 1,7 or both 3,5 (reach 40.6% of multisets).
Then with t = (a+sigma)/8 and c_e = e*a mod 8 in {2,...,6}, the non-divisible runner e is
safe while  1 - c_e < e*sigma < 7 - c_e, i.e.  sigma in ( (1-c_e)/e , (7-c_e)/e ).
The divisible runner 8m needs ||m sigma|| >= 1/8.

Near sigma = 0 EVERY divisible runner is maximally unsafe (m*0 = 0), so we must leave
sigma = 0, and the first admissible sigma for a single m is 1/(8m).  The window's half-width
is room/V.  So the lemma can only fire when roughly

        min over divisible of 1/(8m)  <  min over non-divisible of room_e/e ,

i.e. the divisible speeds must be LARGE relative to the non-divisible ones.  LRC(d+1) gives
sigma somewhere on the circle; it says nothing about landing in this window.  Measured here.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd

UNITS={1,3,5,7}
def slack_a(Rnon):
    if not (Rnon & {1,7}): return 1
    if not (Rnon & {3,5}): return 3
    return None

def window_fires(E, a):
    """is there sigma in the non-divisible window with ||m sigma||>=1/8 for all divisible?"""
    nd=[e for e in E if e%8!=0]; dv=[e//8 for e in E if e%8==0]
    lo=F(-10); hi=F(10)
    for e in nd:
        c=(e*a)%8
        if c in (0,1,7): return None          # no slack: lemma hypothesis violated
        lo=max(lo, F(1-c,e)); hi=min(hi, F(7-c,e))
    if lo>=hi: return False
    # intersect with { ||m sigma|| >= 1/8 } for each divisible m, by interval arithmetic
    cur=[(lo,hi)]
    for m in dv:
        arcs=[]
        j=int(lo*m)-2
        while F(8*j+1,8*m) < hi+1:
            arcs.append((F(8*j+1,8*m), F(8*j+7,8*m))); j+=1
        out=[]
        for (A,B) in cur:
            for (C,D) in arcs:
                l=max(A,C); r=min(B,D)
                if l<r: out.append((l,r))
        cur=out
        if not cur: return False
    return True

tot=0; hyp=0; fired=0; ex_fail=None
for E in combinations(range(1,27),7):
    if reduce(gcd,E)!=1: continue
    if not any(e%8==0 for e in E): continue
    Rnon={e%8 for e in E if e%8!=0}
    a=slack_a(Rnon)
    tot+=1
    if a is None: continue
    hyp+=1
    r=window_fires(list(E),a)
    if r: fired+=1
    elif ex_fail is None: ex_fail=(E,a,Rnon)
print(f"Case-2 tuples in [1..26]        : {tot}")
print(f"  Slack Lemma HYPOTHESIS holds  : {hyp}  ({100*hyp/tot:.1f}%)")
print(f"  ...and the WINDOW actually fires: {fired}  ({100*fired/hyp:.1f}% of those, "
      f"{100*fired/tot:.1f}% of Case 2)")
if ex_fail:
    E,a,R=ex_fail
    print(f"\n  first failure: E = {E}, a = {a}, R_non = {sorted(R)}")
    nd=[e for e in E if e%8!=0]; dv=[e//8 for e in E if e%8==0]
    print(f"    non-divisible {nd} (max {max(nd)});  divisible m = {dv}")
    print(f"    need sigma >= 1/(8m) = {[str(F(1,8*m)) for m in dv]}"
          f"  but window half-width ~ 1/max(nd) = {F(1,max(nd))}")
