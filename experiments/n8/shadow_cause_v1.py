"""What CAUSES a flank to be shadowed?
Claim to test: shadowing is not a density effect -- the union density is ~0.8 everywhere.
It is a SMALL-L effect.  L = lcm_j(q_j), q_j = e/gcd(|d_j|,e), and L | e.
Shadowing needs 6 movers to cover ALL L openings with no opening missed, so it needs L small
AND the blocked sets to tile.  Measure P(shadowed | L) and the L-distribution by outcome."""
from math import gcd, lcm
from functools import lru_cache
from collections import Counter
import random, statistics as st
@lru_cache(maxsize=None)
def cls(a,q):
    M=8*q
    return frozenset(k for k in range(q) if (lambda r:min(r,M-r)<q)((a*(8*k+1))%M))
def flank(ds,e):
    qs=[e//gcd(abs(d),e) for d in ds]
    L=lcm(*qs); cov=set()
    for d,q in zip(ds,qs):
        g=e//q                       # gcd(|d|,e); a = d/g is the reduced numerator
        c=cls((d//g)%(8*q), q)
        cov|={k for k in range(L) if k%q in c}
    return L,qs,(len(cov)==L)
random.seed(8)
shadL=[]; clearL=[]; byL=Counter(); shByL=Counter(); maxq_sh=[]
for _ in range(30000):
    hi=10**random.choice([1,1,2,2,3,4])
    v=random.sample(range(-hi,hi+1),8); s=random.randrange(8)
    ds=[v[j]-v[s] for j in range(8) if j!=s]
    for e in sorted({abs(d) for d in ds}):
        L,qs,sh=flank(ds,e)
        b=min(L,64) if L<64 else (64 if L<128 else (128 if L<512 else 512))
        byL[b]+=1
        if sh: shByL[b]+=1; shadL.append(L); maxq_sh.append(max(qs))
        else: clearL.append(L)
print(f"flanks examined: {len(shadL)+len(clearL)};  shadowed: {len(shadL)} "
      f"({100*len(shadL)/(len(shadL)+len(clearL)):.2f}%)")
print(f"  median L  shadowed = {st.median(shadL):.0f}   clear = {st.median(clearL):.0f}")
print(f"  max L ever shadowed = {max(shadL)};   99th pct of shadowed L = "
      f"{sorted(shadL)[int(0.99*len(shadL))]}")
print(f"  max q among shadowed flanks: min={min(maxq_sh)} (never below 8: {min(maxq_sh)>=8})")
print("\n  P(shadowed | L):")
for b in sorted(byL):
    if byL[b]>=30:
        print(f"    L~{b:<5d} n={byL[b]:7d}   shadowed {100*shByL[b]/byL[b]:6.2f}%")
print("\n  L-distribution of shadowed flanks (top values):")
print("   ",Counter(shadL).most_common(12))
