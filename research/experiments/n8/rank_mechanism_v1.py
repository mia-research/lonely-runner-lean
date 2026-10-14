"""WHY does clear-rate rise with flank size?  Measure the candidate drivers per rank.
For flank e with movers d_j:  q_j = e/gcd(|d_j|,e),  L = lcm(q_j) | e.
Blocked openings of mover j = a set of classes mod q_j; density = (#classes)/q_j.
Shadowed iff the union covers all L openings."""
from math import gcd, lcm
from functools import lru_cache
import random
@lru_cache(maxsize=None)
def cls(dm,q):
    """blocked classes mod q for a mover whose ratio has reduced denominator q, dm = d mod 8q"""
    M=8*q
    return frozenset(k for k in range(q) if (lambda r:min(r,M-r)<q)((dm*(8*k+1))%M))
def analyse(ds,e):
    qs=[e//gcd(abs(d),e) for d in ds]
    L=lcm(*qs)
    cov=set(); dens=[]
    for d,q in zip(ds,qs):
        c=cls((d*(q*(e//q) and 1) or 0,q)[0] if False else (d//(e//q))%(8*q), q)
        dens.append(len(c)/q)
        cov|={k for k in range(L) if k%q in c}
    return L,qs,dens,len(cov)/L,(len(cov)==L)
# sanity: reduced mover d/(e/q) must be an integer
random.seed(4)
print("counterexample re-check:")
ds=[-4,1,3,4,5,7,8]; e=8
L,qs,dens,uc,sh=analyse(ds,e)
print(f"  ds={ds} e={e}: q_j={qs}, L={L}, union coverage={uc:.3f}, SHADOWED={sh}")
print()
print(" rank  clear%    mean e   mean L  mean max q   mean sum(density)  mean union cov")
import statistics as st
R={r:[] for r in range(7)}
for _ in range(20000):
    hi=10**random.choice([1,2,3,4])
    v=random.sample(range(-hi,hi+1),8); s=random.randrange(8)
    ds=[v[j]-v[s] for j in range(8) if j!=s]
    order=sorted(range(7), key=lambda i:-abs(ds[i]))
    for r,i in enumerate(order):
        e=abs(ds[i])
        L,qs,dens,uc,sh=analyse(ds,e)
        R[r].append((not sh, e, L, max(qs), sum(dens), uc))
for r in range(7):
    A=R[r]
    print(f"   {r}   {100*st.mean(a[0] for a in A):6.2f}%  "
          f"{st.mean(a[1] for a in A):9.0f} {st.mean(a[2] for a in A):8.0f} "
          f"{st.mean(a[3] for a in A):9.0f}   {st.mean(a[4] for a in A):14.3f}  {st.mean(a[5] for a in A):13.3f}")
