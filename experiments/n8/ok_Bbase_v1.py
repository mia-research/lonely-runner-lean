r"""
ok_Bbase_v1 -- route (B): the ov >= 5 family, from the inside.

Such an E has five speeds in lambda*T for a tight instance T, plus two free speeds.  |G| is
scale-invariant, so |G(lambda T')| = |G(T')| and the base contributes a fixed measure per
5-subset T'.  There are 3 tight instances x C(7,5) = 63 base sets.  Adding the two free
runners can only shrink G.  This tabulates the base measures and the worst case after the
two free runners are added, over all admissible completions inside a box.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd

TIGHT=[(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]
def arcs(e): return [(F(8*j+1,8*e), F(8*j+7,8*e)) for j in range(e)]
def inter(A,B):
    out=[]; i=j=0
    while i<len(A) and j<len(B):
        lo=max(A[i][0],B[j][0]); hi=min(A[i][1],B[j][1])
        if lo<hi: out.append((lo,hi))
        if A[i][1]<B[j][1]: i+=1
        else: j+=1
    return out
def Gset(E):
    cur=arcs(E[0])
    for e in E[1:]:
        cur=inter(cur,arcs(e))
        if not cur: return []
    return cur
def meas(iv): return sum((b-a for a,b in iv), F(0))

print("base measures |G(T')| over the 63 five-subsets of the three tight instances:")
base={}
for T in TIGHT:
    for T5 in combinations(T,5):
        base[(T,T5)]=meas(Gset(list(T5)))
vals=sorted(base.items(), key=lambda kv: kv[1])
print(f"  min |G(T')| = {vals[0][1]} = {float(vals[0][1]):.6f}  at {vals[0][0][1]} of {vals[0][0][0]}")
print(f"  max |G(T')| = {vals[-1][1]} = {float(vals[-1][1]):.6f}  at {vals[-1][0][1]}")
import statistics
print(f"  mean = {statistics.mean(float(v) for v in base.values()):.6f}   "
      f"(for reference (3/4)^5 = {0.75**5:.6f})")

print("\nworst case after adding the two free speeds (lambda=1,2; free speeds <= 24):")
tgt=F(93,14560)
worst=None; n=0
for T in TIGHT:
    for lam in (1,2):
        for T5 in combinations(T,5):
            S5=[lam*x for x in T5]
            if max(S5)>24: continue
            for f1,f2 in combinations([x for x in range(1,25) if x not in S5],2):
                E=sorted(S5+[f1,f2])
                if len(set(E))<7: continue
                if reduce(gcd,E)!=1: continue
                if not any(e%8==0 for e in E): continue
                n+=1
                g=meas(Gset(E))
                if worst is None or g<worst[0]: worst=(g,tuple(E),T,lam,T5)
g,E,T,lam,T5=worst
print(f"  {n} completions examined")
print(f"  min |G| = {g} = {float(g):.6f}   at E = {E}")
print(f"     base {lam}*{T5} from T = {T}")
print(f"  target 93/14560 = {float(tgt):.6f};  ratio {float(g/tgt):.3f}")
print(f"  {'MEETS the target' if g>=tgt else 'BELOW the target -- would be a new extremum'}")
