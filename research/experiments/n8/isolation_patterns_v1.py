"""Owner: "For AP there are only 4 arrangements of global isolation, two patterns and two
inversions.  What about grids -- does it change the arrangement of the isolation pattern?"

At t = p/(n g) runner i sits at (pi(i)*p mod n)/n, where pi(i) = u_i mod n is the residue
(WHICH_GRIDS sec2).  So the pattern is  pi  followed by multiplication by p, and the four
instants are p in (Z/8)^x = {1,3,5,7}."""
from math import gcd
from itertools import combinations

def reduced(v):
    g=0
    for a,b in combinations(v,2): g=gcd(g,abs(b-a))
    return [(x-v[0])//g for x in v], g
def pattern(v,p):
    u,g=reduced(v)
    pos=[(x*p)%8 for x in u]                 # runner i sits at pos[i]/8
    order=[None]*8
    for i,s in enumerate(pos): order[s]=i    # who is at slot s
    return tuple(order)
def inverted(t):   # reflection of the circle: slot s -> slot (-s) mod 8
    return tuple(t[(-s)%8] for s in range(8))

print("=== the AP (0..7): the four isolation patterns ===")
AP=list(range(8))
pats={}
for p in (1,3,5,7):
    pats[p]=pattern(AP,p)
    print(f"   p = {p}:  runners around the circle  {pats[p]}")
print(f"   is p=7 the inversion of p=1 ?  {inverted(pats[1])==pats[7]}")
print(f"   is p=5 the inversion of p=3 ?  {inverted(pats[3])==pats[5]}")
print("   -> two patterns and two inversions, exactly as stated.")

print()
print("=== a grid with a NON-identity residue map ===")
G=[0,2,3,4,5,6,7,9]
u,g=reduced(G)
print(f"   v = {G}   reduced {u}   residues {[x%8 for x in u]}   complete? {len(set(x%8 for x in u))==8}")
gp={}
for p in (1,3,5,7):
    gp[p]=pattern(G,p)
    print(f"   p = {p}:  {gp[p]}")
print(f"   is p=7 the inversion of p=1 ?  {inverted(gp[1])==gp[7]}")
print(f"   is p=5 the inversion of p=3 ?  {inverted(gp[3])==gp[5]}")
print(f"   same four patterns as the AP ?  {set(gp.values())==set(pats.values())}")

print()
print("=== over ALL globally isolated 8-subsets of [0,24) ===")
seen=set(); nz=0; tot=0; inv_ok=0
for v in combinations(range(0,24),8):
    u,g=reduced(v)
    if len(set(x%8 for x in u))!=8: continue
    tot+=1
    P={p:pattern(v,p) for p in (1,3,5,7)}
    if len(set(P.values()))!=4: nz+=1
    if inverted(P[1])==P[7] and inverted(P[3])==P[5]: inv_ok+=1
    seen.add(tuple(sorted(P.values())))
print(f"   globally isolated arrangements: {tot}")
print(f"   with fewer than 4 DISTINCT patterns: {nz}")
print(f"   with 'p=7 inverts p=1 and p=5 inverts p=3': {inv_ok} of {tot}")
print(f"   distinct SETS of four patterns realised: {len(seen)}")
print(f"   (the number of residue maps pi -- i.e. of orderings -- is what varies)")
