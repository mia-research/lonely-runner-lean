"""What IS the true bound on runners per residue slot, for primitive arrangements?

This matters beyond bookkeeping.  BS Corollary 3's hypothesis is "every valuation level below the
top has at most 3 elements" (BS_TRANSFER_v2 sec 3 -- the same 3 at n=8).  A parallel session
reported max 3 per slot mod 8, which if true would feed that hypothesis directly.  It is forced by
their v <= 16 bound.  So: what is the real maximum?

All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from math import gcd
from itertools import combinations
from collections import Counter
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
print("  upper bound by pure arithmetic:")
print("    all 8 in one slot => every pairwise difference divisible by 8 => g >= 8,")
print("    contradicting primitivity (g = 1).  So the maximum is at most 7.\n")
print("  witnesses (primitive, all speeds positive):")
for k in range(2,8):
    # k runners congruent mod 8, the rest breaking the gcd
    base=[1+8*t for t in range(k)]
    rest=[]
    x=2
    while len(base)+len(rest)<8:
        if x not in base and (x-1)%8!=0: rest.append(x)
        x+=1
    v=speeds(base+rest)
    g=gcd_all(v); u=[(y-min(v))//g for y in v]
    c=Counter(y%8 for y in u)
    ok = (g==1 and max(c.values())==k)
    print(f"    k={k}: v={str(list(v)):<34} g={g}  slot sizes {dict(sorted(c.items()))}  max={max(c.values())}  {'OK' if ok else 'MISMATCH'}")
print()
print("  => the true bound is 7, not 3.  BS Corollary 3's analogue needs <= 3 per level,")
print("     so the level sizes are NOT bounded where that argument would require it.")
