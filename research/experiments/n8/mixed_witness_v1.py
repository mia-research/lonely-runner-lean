"""Mixed-scale divisor-closed profiles: WHERE is the witness?
Every one of them clears. Find what locates the witness, natively: L(b), U(b), the largest
modulus, the lcm. Candidate read: the witness sits just above L(b_max), because the largest
modulus confines q to [L(b_max), U(b_max)] and the small moduli are short-period obstacles."""
from math import lcm, gcd
from functools import reduce
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def clears(bs,q): return all(L(b) <= q % b <= U(b) for b in bs)
random.seed(9)
rows=[]
for _ in range(40000):
    m=random.choice([24,36,48,60,72,96,120,144,180,240,360,504,720,840])
    divs=[d for d in range(2,m+1) if m%d==0]
    if len(divs)<5: continue
    bs=sorted(random.sample(divs,5))
    if max(bs)<=9 or min(bs)>=10: continue          # mixed only
    M=reduce(lcm,bs)
    if M>400000: continue
    bmax=max(bs)
    q=next((x for x in range(M) if clears(bs,x)), None)
    if q is None: rows.append((bs,None,None,None)); continue
    # walk up from L(bmax)
    w=next((x for x in range(L(bmax), M+L(bmax)) if clears(bs,x%M)), None)
    rows.append((bs,q,w,bmax))
ok=[r for r in rows if r[1] is not None]
print(f"mixed profiles examined: {len(rows)};  with a witness: {len(ok)};  without: {len(rows)-len(ok)}")
import statistics as st
print(f"\n  smallest witness q: median {st.median(r[1] for r in ok):.0f}, "
      f"max {max(r[1] for r in ok)}")
d=[r[2]-L(r[3]) for r in ok]
print(f"  walk length from L(b_max) to the first clearing q:")
print(f"     median {st.median(d):.0f}   mean {st.mean(d):.1f}   max {max(d)}   "
      f"zero (L(b_max) itself clears): {100*sum(1 for x in d if x==0)/len(d):.1f}%")
import collections
c=collections.Counter(d)
print(f"     distribution: {sorted(c.items())[:12]}")
print(f"\n  is the walk bounded by the smallest modulus?  walk < min(bs): "
      f"{100*sum(1 for r,dd in zip(ok,d) if dd < min(r[0]))/len(ok):.1f}%")
print(f"  walk < lcm of the non-maximal moduli: "
      f"{100*sum(1 for r,dd in zip(ok,d) if dd < reduce(lcm,[b for b in r[0] if b!=r[3]] or [1]))/len(ok):.1f}%")
worst=max(zip(d,ok))
print(f"\n  longest walk: {worst[0]} steps, profile {worst[1][0]}, b_max={worst[1][3]}, "
      f"L(b_max)={L(worst[1][3])}, first clear q={worst[1][2]}")
