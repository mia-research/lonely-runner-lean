# Owner: faster runners get in and out of the way faster, so they leave more opportunity.
# In the flank picture, stepping k by 1 moves runner a by (a mod b).  Slow runner -> small step
# -> blocks LONG RUNS of consecutive openings.  Fast runner -> big step -> SCATTERED blocks.
# Measure run structure against speed.
from math import gcd
import random
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def runs(ds_a,b):
    blocked=[k for k in range(b) if not clear(ds_a,b,k)]
    if not blocked: return 0,0.0
    bs=set(blocked); nr=sum(1 for k in blocked if (k-1)%b not in bs)
    return nr, len(blocked)/max(1,nr)
rng=random.Random(3)
rows=[]
for _ in range(400):
    ds=sorted(rng.sample(range(1,200),7)); g=gcd(*ds); ds=[x//g for x in ds]
    b=max(ds)
    if b<40: continue
    for a in ds:
        if a==b: continue
        nr,avg = runs(a,b)
        rows.append((a/b, nr, avg, len([k for k in range(b) if not clear(a,b,k)])/b))
rows.sort()
print(f"{len(rows)} (runner, flank) pairs at b = max(ds), bucketed by speed ratio a/b")
print(f"{'a/b range':>14} {'n':>5} {'#runs':>8} {'avg run len':>12} {'blocked frac':>13}")
import statistics
B=[(0,.1),(.1,.2),(.2,.35),(.35,.5),(.5,.7),(.7,1.0)]
for lo,hi in B:
    v=[r for r in rows if lo<=r[0]<hi]
    if len(v)<20: continue
    print(f"{lo:>6.2f}-{hi:<7.2f} {len(v):>5} {statistics.median(r[1] for r in v):>8.1f} "
          f"{statistics.median(r[2] for r in v):>12.2f} {statistics.median(r[3] for r in v):>13.3f}")
print()
print("  -> blocked FRACTION is the same (~1/4) for all speeds; the SHAPE differs:")
print("     slow runners block few long runs, fast runners block many short ones.")
