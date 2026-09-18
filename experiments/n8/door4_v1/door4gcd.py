# Runner a's condition depends on k only through k mod (b/gcd(a,b)): a*k mod b ranges over
# multiples of g = gcd(a,b).  So the WHOLE system depends on k mod L, L = lcm_i (b/g_i), and
# L | b.  If L is small there are few effective choices of k and the conditions can conspire.
# Test: does L (the effective freedom) predict the deficiency?
from math import gcd
import random
def lcm(x,y): return x*y//gcd(x,y)
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
rows=[]
rng=random.Random(77)
for _ in range(20000):
    ds=sorted(rng.sample(range(1,90),7)); g0=gcd(*ds); ds=[x//g0 for x in ds]
    b=max(ds)
    if b<8: continue
    L=1
    for a in ds: L=lcm(L, b//gcd(a,b))
    cnt=sum(1 for k in range(b) if all(clear(a,b,k) for a in ds))
    pred=b*(0.75**6)
    rows.append((L/b, cnt, pred, b, tuple(ds)))
# bucket by effective freedom L/b
import collections
buck=collections.defaultdict(list)
for Lb,cnt,pred,b,ds in rows:
    key = "L = b (full)" if abs(Lb-1)<1e-9 else ("L >= b/2" if Lb>=0.5 else ("L >= b/4" if Lb>=0.25 else "L < b/4"))
    buck[key].append((cnt,pred,cnt/pred if pred>0 else 0,b,ds))
print(f"{len(rows)} flanks b = max(ds)")
for key in ("L = b (full)","L >= b/2","L >= b/4","L < b/4"):
    v=buck.get(key,[])
    if not v: continue
    rs=sorted(x[2] for x in v)
    zero=sum(1 for x in v if x[0]==0)
    print(f"  {key:14s} n={len(v):6d}  actual/predicted: min {rs[0]:.3f} median {rs[len(rs)//2]:.3f}   zero-count flanks {zero}")
print()
worst=sorted(rows, key=lambda r: r[1]/r[2] if r[2]>0 else 9)[:5]
print("five worst flanks by actual/predicted:")
for Lb,cnt,pred,b,ds in worst:
    gs=[gcd(a,b) for a in ds]
    print(f"   ds={ds} b={b}  count {cnt} vs pred {pred:.2f} (ratio {cnt/pred:.3f})  L/b={Lb:.3f}  gcds={gs}")
print()
print("does ANY flank of these sets do better?  (we get to choose the flank)")
for Lb,cnt,pred,b,ds in worst:
    tot={bb: sum(1 for k in range(bb) if all(clear(a,bb,k) for a in ds)) for bb in ds}
    print(f"   ds={ds}: per-flank counts {tot}  -> best {max(tot.values())}")
