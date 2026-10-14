"""THE RULE the search is implicitly using.

For INTEGER readings, a gap between consecutive bad intervals runs from (8m+1)/s to (8m'-1)/s', and

     width = [ s(8m'-1) - s'(8m+1) ] / (s.s')

The numerator is an INTEGER, and positive when there is a gap -- so it is at least 1:

     ANY GAP HAS WIDTH >= 1/(s.s')

Verify on the minimiser's four gaps, then across many profiles."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from itertools import combinations
import random
def gaps_with_sources(S):
    iv=[]
    for s in S:
        k=0
        while F(8*k-1,1)/s <= 8:
            a,b=F(8*k-1,1)/s, F(8*k+1,1)/s
            if b>1 and a<7: iv.append((a,b,s,k))
            k+=1
    iv.sort()
    out=[]; pos=F(1); src=None
    for a,b,s,k in iv:
        if a>pos and pos>=1:
            out.append((pos,a,src,(s,k)))
        if b>pos: pos, src = b,(s,k)
    if pos<7: out.append((pos,F(7),src,None))
    return out
print("  minimiser [3,4,5,7,11,24] -- each gap, with the two readings that bound it\n")
S=[F(x) for x in [3,4,5,7,11,24]]
tot=F(0)
for lo,hi,left,right in gaps_with_sources(S):
    w=hi-lo; tot+=w
    if left and right:
        s,k=left; s2,k2=right
        N=s*(8*k2-1)-s2*(8*k+1)
        print(f"    ({lo}, {hi})  width {w}   left comb s={s} m={k}, right comb s'={s2} m'={k2}")
        print(f"        numerator N = s(8m'-1) - s'(8m+1) = {N}   and 1/(s.s') = {F(1,int(s*s2))}   "
              f"{'width = N/(s.s’)' if w==F(int(N),int(s*s2)) else 'MISMATCH'}")
print(f"    total {tot}   (half of the joint 53/462 = {F(53,924)})  {tot==F(53,924)}")
print()
print("  now check the rule across many profiles: is every gap width >= 1/(s.s')?")
rng=random.Random(99); ok=0; tot_g=0; viol=0; smallest=None
for _ in range(4000):
    prof=sorted(rng.sample(range(2,60),6))
    S=[F(x) for x in prof]
    for lo,hi,left,right in gaps_with_sources(S):
        if not (left and right): continue
        s,k=left; s2,k2=right
        w=hi-lo; bound=F(1,int(s*s2))
        tot_g+=1
        if w>=bound: ok+=1
        else: viol+=1
        if smallest is None or w<smallest[0]: smallest=(w,prof,int(s),int(s2))
print(f"    {tot_g} gaps examined:  width >= 1/(s.s') in {ok},  violations {viol}")
print(f"    smallest gap seen: {smallest[0]} = {float(smallest[0]):.8f}  in {smallest[1]}  "
      f"between s={smallest[2]} and s'={smallest[3]}  (1/(s.s') = {F(1,smallest[2]*smallest[3])})")
