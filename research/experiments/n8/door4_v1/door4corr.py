# Door 4 at flank b: runner a is clear at opening k iff (a*k+q) mod b lies in an interval of
# relative length 3/4.  Six such conditions.  Heuristic (3/4)^6 matched observation - so ask
# whether the conditions are PAIRWISE near-independent, which is what a second-moment argument
# would need.
from math import gcd
import random, statistics
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def marginal(a,b):
    return sum(1 for k in range(b) if clear(a,b,k))/b
def joint(a1,a2,b):
    return sum(1 for k in range(b) if clear(a1,b,k) and clear(a2,b,k))/b
rng=random.Random(21)
devs=[]; worst=None; marg=[]
for _ in range(400):
    ds=sorted(rng.sample(range(1,90),7)); g=gcd(*ds); ds=[x//g for x in ds]
    b=max(ds); others=[a for a in ds if a!=b]
    if b<8: continue
    for i in range(len(others)):
        marg.append(marginal(others[i],b))
        for j in range(i+1,len(others)):
            a1,a2=others[i],others[j]
            p1,p2=marginal(a1,b),marginal(a2,b)
            p12=joint(a1,a2,b)
            d=p12-p1*p2
            devs.append(d)
            if worst is None or abs(d)>abs(worst[0]): worst=(d,a1,a2,b,p1,p2,p12)
devs.sort()
print(f"pairs measured: {len(devs)}")
print(f"  marginal clear density : mean {statistics.mean(marg):.4f}  (3/4 = 0.75)")
print(f"  joint minus product    : mean {statistics.mean(devs):+.4f}  median {devs[len(devs)//2]:+.4f}")
print(f"                           min {devs[0]:+.4f}  max {devs[-1]:+.4f}")
print(f"  |deviation| > 0.05     : {sum(1 for d in devs if abs(d)>0.05)}/{len(devs)}")
print(f"  |deviation| > 0.15     : {sum(1 for d in devs if abs(d)>0.15)}/{len(devs)}")
print(f"  worst pair: a1={worst[1]} a2={worst[2]} b={worst[3]}  p1={worst[4]:.3f} p2={worst[5]:.3f} p12={worst[6]:.3f} (product {worst[4]*worst[5]:.3f})")
print()
# does the actual count of lonely openings track the independent prediction?
print("count of lonely openings at b=max(ds) vs the independent prediction b*(3/4)^6:")
rows=[]
rng2=random.Random(33)
for _ in range(2000):
    ds=sorted(rng2.sample(range(1,90),7)); g=gcd(*ds); ds=[x//g for x in ds]
    b=max(ds)
    if b<8: continue
    cnt=sum(1 for k in range(b) if all(clear(a,b,k) for a in ds))
    pred=b*(0.75**6)
    rows.append((cnt,pred))
r=[c/p for c,p in rows if p>0]; r.sort()
print(f"  ratio actual/predicted : min {r[0]:.3f}  10th {r[int(.1*len(r))]:.3f}  median {r[len(r)//2]:.3f}  max {r[-1]:.3f}")
print(f"  flanks with ZERO lonely openings: {sum(1 for c,_ in rows if c==0)}/{len(rows)}")
