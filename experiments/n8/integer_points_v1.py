"""A FINITE necessary condition.

The region [1,7] u [9,15] contains 14 integer points: 1..7 and 9..15.  Each must be blocked by some
reading, else it is clear and R < 16.  Blocking at integer R needs |R.s - 8m| < 1, i.e.

        s  in  ( (8m-1)/R , (8m+1)/R )   for some integer m.

So each reading s blocks a COMPUTABLE subset of the 14 points.  Question: can six readings
(s in (1,8), since s_1 = 1 is fixed and s_7 = S) block all 14?

If NOT, band 2 is impossible and the argument is a finite check.
NOTE s_1 = 1 blocks R with |R - 8m| < 1, i.e. R in {1,7,9,15} (integers within 1 of 0 or 8 or 16).
So s_1 already handles four of them -- check that first."""
import sys; sys.path.insert(0,'experiments/n8')
import numpy as np
from itertools import combinations
PTS=[r for r in range(1,16) if r!=8]
def blocks(s):
    out=set()
    for R in PTS:
        for m in range(0,40):
            if (8*m-1)/R < s < (8*m+1)/R: out.add(R); break
    return frozenset(out)
print(f"  the 14 integer points: {PTS}\n")
print(f"  s_1 = 1 blocks: {sorted(blocks(1.0))}")
rem=[r for r in PTS if r not in blocks(1.0)]
print(f"  remaining to block by the other six: {rem}  ({len(rem)} points)\n")
# what can a single reading block?
grid=np.arange(1.0001, 8.0, 1e-5)
sets={}
for s in grid:
    b=blocks(s) & frozenset(rem)
    if b: sets.setdefault(b, s)
print(f"  distinct blocking-sets achievable by one reading in (1,8): {len(sets)}")
big=sorted(sets.items(), key=lambda z:-len(z[0]))[:6]
for b,s in big:
    print(f"    s = {s:.5f} blocks {sorted(b)}  ({len(b)} points)")
print()
# can six readings cover `rem`?
target=set(rem)
cand=list(sets.items())
best=(0,None)
import random
rng=random.Random(7)
# exact-ish: greedy + randomised restarts
for _ in range(20000):
    cur=set(); pick=[]
    pool=cand[:]
    rng.shuffle(pool)
    while len(pick)<6:
        b=max(pool, key=lambda z: len(z[0]-cur))
        if not (b[0]-cur): break
        cur|=b[0]; pick.append(b[1])
    if len(cur)>best[0]: best=(len(cur),list(pick))
    if cur==target: break
print(f"  best coverage of the {len(rem)} remaining points by six readings: {best[0]}")
print(f"    readings {[round(x,5) for x in best[1]]}" if best[1] else "")
print(f"    ALL {len(rem)} blocked? {best[0]==len(rem)}")
