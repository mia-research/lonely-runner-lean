"""The -7 opening.
Let L be a common multiple of the reduced denominators q_j = e/gcd(|d_j|,e).  Then e | L*d_j, so
at A = 8L - 7 = 8(L-1)+1 we have d*A = 8L*d - 7d = -7d  (mod 8e).  Hence

        inWay d A e   <=>   dist(7d, 8e*Z) < e

-- a criterion with NO opening index in it at all.  Test the identity, then count how many of a
subject's flanks are clear at this one opening."""
from math import gcd, lcm
import random
def inWay(d,A,e):
    M=8*e; r=(d*A)%M; return min(r,M-r)<e
def crit(d,e):
    M=8*e; r=(7*d)%M; return min(r,M-r)<e
random.seed(3)
bad=0; tot=0
for _ in range(120000):
    e=random.randint(1,300)
    ds=[d for d in (random.randint(-900,900) for _ in range(7)) if d!=0]
    if not ds: continue
    L=lcm(*[e//gcd(abs(d),e) for d in ds]); A=8*L-7
    for d in ds:
        tot+=1
        if inWay(d,A,e)!=crit(d,e): bad+=1
print(f"[identity] inWay d (8L-7) e  <=>  dist(7d,8eZ) < e   over {tot} movers: "
      f"{'HOLDS' if bad==0 else f'FAILS {bad}'}")

print("\n[flank census] integer arrangements of 8 distinct runners; for each subject, how many of")
print("its 7 flanks |d_j| are clear at the -7 opening?")
from collections import Counter
for hi in (12, 30, 100, 1000):
    cnt=Counter(); worst=None
    for _ in range(40000):
        v=random.sample(range(-hi,hi+1),8)
        for s in range(8):
            ds=[v[j]-v[s] for j in range(8) if j!=s]
            flanks=sorted({abs(d) for d in ds})
            c=sum(1 for e in flanks if all(not crit(d,e) for d in ds))
            cnt[c]+=1
            if worst is None or c<worst[0]: worst=(c,v[:],s)
    print(f"  range +-{hi:4d}: clear-flank counts {dict(sorted(cnt.items()))}"
          f"   min={worst[0]}")
    if worst[0]==0: print(f"      ZERO at v={worst[1]} subject index {worst[2]}")
