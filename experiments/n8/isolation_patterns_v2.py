"""v2 -- v1 used 0 as a SPEED, which the framework forbids (sec 6A; register item 12, a standing
ban).  The conjecture is eight distinct POSITIVE speeds.  Here every enumeration starts at 1.

Also checks explicitly that the pattern analysis is shift-invariant, so we know whether v1's
numbers were wrong or only its presentation."""
from math import gcd
from itertools import combinations

def reduced(v):
    g=0
    for a,b in combinations(v,2): g=gcd(g,abs(b-a))
    return [(x-min(v))//g for x in v], g
def pattern(v,p):
    u,g=reduced(v)
    pos=[(x*p)%8 for x in u]
    order=[None]*8
    for i,s in enumerate(pos): order[s]=i
    return tuple(order)
def inverted(t): return tuple(t[(-s)%8] for s in range(8))
def isolated(v):
    u,g=reduced(v); return len(set(x%8 for x in u))==8

print("=== does a common shift change anything? ===")
base=[1,2,3,4,5,6,7,8]
for c in (0,1,5,100):
    v=[x+c for x in base]
    print(f"   speeds {v[:3]}...  patterns {[pattern(v,p) for p in (1,3)]}")
print("   -> the reduction subtracts min(v) and divides by g, so a common shift cancels.")
print("      v1's NUMBERS are unaffected; its FRAME was illegal.  Both matter, differently.")

print()
print("=== the AP, stated legally: speeds 1..8 ===")
AP=[1,2,3,4,5,6,7,8]
P={p:pattern(AP,p) for p in (1,3,5,7)}
for p in (1,3,5,7): print(f"   p = {p}:  {P[p]}")
print(f"   p=7 inverts p=1: {inverted(P[1])==P[7]}     p=5 inverts p=3: {inverted(P[3])==P[5]}")

print()
print("=== a grid with a non-identity residue map, POSITIVE speeds ===")
G=[1,3,4,5,6,7,8,10]
u,g=reduced(G)
print(f"   speeds {G}   reduced {u}   residues {[x%8 for x in u]}   globally isolated: {isolated(G)}")
Q={p:pattern(G,p) for p in (1,3,5,7)}
for p in (1,3,5,7): print(f"   p = {p}:  {Q[p]}")
print(f"   p=7 inverts p=1: {inverted(Q[1])==Q[7]}     p=5 inverts p=3: {inverted(Q[3])==Q[5]}")
print(f"   same four patterns as the AP: {set(Q.values())==set(P.values())}")

print()
print("=== all globally isolated 8-subsets of POSITIVE integers [1,24] ===")
seen=set(); nz=0; tot=0; inv=0
for v in combinations(range(1,25),8):
    if not isolated(v): continue
    tot+=1
    R={p:pattern(v,p) for p in (1,3,5,7)}
    if len(set(R.values()))!=4: nz+=1
    if inverted(R[1])==R[7] and inverted(R[3])==R[5]: inv+=1
    seen.add(tuple(sorted(R.values())))
print(f"   globally isolated arrangements (no zero speed): {tot}")
print(f"   fewer than 4 distinct patterns: {nz}")
print(f"   inversion structure holds: {inv} of {tot}")
print(f"   distinct SETS of four patterns: {len(seen)}")

print()
print("=== and the minimal-spread claim, restated legally ===")
best=None; aps=0; n=0
for v in combinations(range(1,17),8):
    if not isolated(v): continue
    u,g=reduced(v); sp=max(u)-min(u)
    if best is None or sp<best: best=sp
for v in combinations(range(1,17),8):
    if not isolated(v): continue
    u,g=reduced(v)
    if max(u)-min(u)==best:
        n+=1
        if sorted(u)==list(range(min(u),min(u)+8)): aps+=1
print(f"   minimal reduced spread among globally isolated POSITIVE arrangements: {best}")
print(f"   attaining it: {n};  of those, consecutive (an AP of gap g): {aps}")
