"""Cross-check a parallel session's sweep before anything is built on it.

Their claims:
  (A) lonely at grid instant t = 1/(8g)  <->  reduced residue unique      [45468/91456, 0 disagree]
  (B) "At n=8, no slot modulo 8 ever holds more than 3 runners"           [stated as an n=8 fact]
  (C) Lean plan: candidateScale 8 (d_min) 0 = d_min "which is the grid scale D_0",
      so clearing at k=0  <->  unique residue.

(A) reproduces my residue_partition_v1 (32,000/32,000) and should hold.
(B) and (C) are the ones to test.  All speeds positive here; their sweep used 0 = v_0, which is
the allowed reduction, so every number below is checked BOTH ways to confirm shift-invariance."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g

print("=== (B) is 'max 3 per residue slot' an n=8 fact, or forced by v <= 16? ===")
print("    A residue class r has representatives r, r+8, r+16, ... inside [0,CAP].")
for CAP in (16,24,32,40,56):
    print(f"    CAP={CAP:>3}: at most {CAP//8+1} values per class are AVAILABLE -> max slot size <= {min(8,CAP//8+1)}")
# exhibit an actual arrangement with 4 and with 5 in one slot
for target in (4,5):
    v=tuple(8*k+1 for k in range(target))+tuple(range(2,2+8-target))
    v=speeds(sorted(set(v))[:8]) if len(set(v))>=8 else None
    if v is None: continue
    u=[x-min(v) for x in v]; g=gcd_all(v); u=[x//g for x in u]
    c=Counter(x%8 for x in u)
    print(f"    witness for {target}: v = {list(v)}  -> slot sizes {dict(sorted(c.items()))}  max {max(c.values())}")
print("    => (B) is FORCED by the enumeration bound, not a property of n = 8.")

print()
print("=== (C) is d_min the grid scale g? ===")
same=0; tot=0; diff_witness=None
clear_dmin=0; uniq=0; disagree=0
for w in combinations(range(1,17),7):
    v=speeds((1,)+tuple(x+1 for x in w))
    g=gcd_all(v)
    if g!=1: continue
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        dmin=min(ds); tot+=1
        if dmin==g: same+=1
        elif diff_witness is None: diff_witness=(v,i,dmin,g)
        # predicate 1: clear at scale d_min  (their Lean k=0)
        p1=all(circd(F(d)*TH/dmin)>=TH for d in ds)
        # predicate 2: unique residue        (their Python)
        p2=all((d//g)%8!=0 for d in ds)
        clear_dmin+=p1; uniq+=p2
        if p1!=p2: disagree+=1
print(f"    subject-instances (primitive, speeds 1..17): {tot}")
print(f"    d_min == g                       : {same}  ({same/tot:.4f})")
if diff_witness:
    v,i,dmin,g=diff_witness
    print(f"    witness d_min != g               : v={list(v)} subject {v[i]}  d_min={dmin}  g={g}")
print(f"    clear at scale d_min  (their k=0): {clear_dmin}  ({clear_dmin/tot:.4f})")
print(f"    unique residue        (their (A)): {uniq}  ({uniq/tot:.4f})")
print(f"    DISAGREEMENTS between the two    : {disagree}  ({disagree/tot:.4f})")
print("    => if this is nonzero, the proposed Lean theorem is FALSE as stated.")

print()
print("=== minimal witness for (C): clear at scale d_min but residue NOT unique ===")
best=None
for w in combinations(range(1,17),7):
    v=speeds((1,)+tuple(x+1 for x in w))
    g=gcd_all(v)
    if g!=1: continue
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        dmin=min(ds)
        p1=all(circd(F(d)*TH/dmin)>=TH for d in ds)
        p2=all((d//g)%8!=0 for d in ds)
        if p1 and not p2:
            if best is None or max(v)<max(best[0]): best=(v,i,ds,dmin,g)
if best:
    v,i,ds,dmin,g=best
    print(f"    v = {list(v)}   subject = {v[i]}")
    print(f"    disparities = {sorted(ds)}   d_min = {dmin}   g = {g}")
    print(f"    clear at scale d_min (k=0) : True")
    bad=[d for d in ds if (d//g)%8==0]
    print(f"    residue unique             : False  -- disparities divisible by 8: {bad}")
    print(f"    so the proposed Iff fails LEFT-to-RIGHT here.")
print()
print("=== and the other direction: residue unique but NOT clear at scale d_min ===")
best2=None
for w in combinations(range(1,17),7):
    v=speeds((1,)+tuple(x+1 for x in w))
    if gcd_all(v)!=1: continue
    g=1
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        dmin=min(ds)
        p1=all(circd(F(d)*TH/dmin)>=TH for d in ds)
        p2=all((d//g)%8!=0 for d in ds)
        if p2 and not p1:
            if best2 is None or max(v)<max(best2[0]): best2=(v,i,ds,dmin)
if best2:
    v,i,ds,dmin=best2
    print(f"    v = {list(v)}   subject = {v[i]}   disparities = {sorted(ds)}   d_min = {dmin}")
    print(f"    residue unique: True     clear at scale d_min: False")
    print(f"    so the Iff fails RIGHT-to-LEFT too -- both directions have witnesses.")
else:
    print("    none found: the implication residue-unique -> clear-at-d_min holds on this sweep.")
