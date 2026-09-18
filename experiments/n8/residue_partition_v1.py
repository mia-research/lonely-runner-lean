"""Owner: "maybe we are not mapping from AP ideals but from GLOBAL ISOLATION."

Against the AP you get deviations.  Against the GRID of scale g = gcd(differences) an integer
arrangement sits EXACTLY -- zero deviation -- and all the information is in WHICH grid points are
occupied, i.e. the residue pattern mod 8.  So the grid is the reference on which nothing is
approximate.

CLAIM TO TEST.  Runner i is lonely at EVERY grid instant r/(8g), r odd, exactly when its residue
u_i mod 8 is UNIQUE among the eight.  If so, the residue pattern partitions the pack:
   unique residue  -> settled at the grid scale, no cascade needed
   shared residue  -> must change scale
which is precisely MANUSCRIPT sec2.3's open item, "how the fit decides which runners then need
the cascade"."""
from fractions import Fraction as F
from math import floor, gcd
import random
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)

rng=random.Random(404); tot=0; agree=0; mism=[]
settled=Counter(); needc=Counter()
for _ in range(4000):
    v=sorted(rng.sample(range(0,120),8))
    g=0
    for a in range(8):
        for b in range(a+1,8): g=gcd(g,v[b]-v[a])
    if g==0: continue
    u=[(x-v[0])//g for x in v]
    cnt=Counter(x%8 for x in u)
    for i in range(8):
        unique = cnt[u[i]%8]==1
        ds=[F(abs(v[j]-v[i])) for j in range(8) if j!=i]
        lonely_all = all(all(circd(d*(F(r,8*g)))>=TH for d in ds) for r in (1,3,5,7))
        tot+=1
        if unique==lonely_all: agree+=1
        elif len(mism)<3: mism.append((v,i,unique,lonely_all))
        (settled if unique else needc)[1]+=1
print(f"=== 'unique residue mod 8'  <=>  'lonely at EVERY grid instant r/(8g)' ===")
print(f"   {agree} of {tot} agree   ({agree/tot:.6f})")
if mism:
    for v,i,a,b in mism: print(f"   MISMATCH v={v} subject index {i}: unique={a} lonely_all={b}")
print()
print(f"   runners with a UNIQUE residue (settled at the grid scale) : {settled[1]}  ({settled[1]/tot:.4f})")
print(f"   runners SHARING a residue   (must change scale)           : {needc[1]}  ({needc[1]/tot:.4f})")
print()
print("=== the partition on the cases on file ===")
for name,v in [("(11,21,22,23,26,34,35,40)",[11,21,22,23,26,34,35,40]),
               ("(1,31,75,97,128,160,176,225)",[1,31,75,97,128,160,176,225]),
               ("(2,3,4,5,6,7,16)+subject 0",[0,2,3,4,5,6,7,16])]:
    g=0
    for a in range(8):
        for b in range(a+1,8): g=gcd(g,abs(v[b]-v[a]))
    u=[(x-v[0])//g for x in v]; res=[x%8 for x in u]; c=Counter(res)
    uniq=[v[i] for i in range(8) if c[res[i]]==1]
    shar=[v[i] for i in range(8) if c[res[i]]>1]
    print(f"   {name}  g={g}  residues {res}")
    print(f"      settled at scale g : {uniq}")
    print(f"      need a new scale   : {shar}")
