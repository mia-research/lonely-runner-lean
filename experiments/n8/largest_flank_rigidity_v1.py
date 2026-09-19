"""How rigid is shadowing the LARGEST flank?
Pool = ratios with |rho| <= 1 (rho mod 8 in [0,1] u [7,8]).  Enumerate ALL shadowing multisets
of size 5 and 6, and report what every one of them must contain."""
from math import gcd, lcm
from itertools import combinations_with_replacement
from collections import Counter
def blocked(a,q):
    M=8*q
    return frozenset(k for k in range(q) if (lambda r: min(r,M-r)<q)((a*(8*k+1))%M))
QMAX=8
pool=[(a,q) for q in range(1,QMAX+1) for a in range(0,8*q) if gcd(a,q)==1
      and not (q==1 and a%8==0) and (a<=q or a>=8*q-q)]
B={m:blocked(*m) for m in pool}
def shadows(ms):
    L=lcm(*[q for _,q in ms])
    cov=set()
    for m in ms:
        q=m[1]; b=B[m]
        cov|={k for k in range(L) if k%q in b}
        if len(cov)==L: return True
    return len(cov)==L
def label(m):
    a,q=m
    return f"{a}/{q}" if a<=q else f"-{8*q-a}/{q}"
for size in (5,6):
    sh=[ms for ms in combinations_with_replacement(pool,size) if shadows(ms)]
    if size==6:   # keep only MINIMAL ones (no shadowing 5-subset)
        from itertools import combinations
        sh=[ms for ms in sh if not any(shadows(s) for s in set(combinations(ms,5)))]
    print(f"\nsize {size}{' (minimal only)' if size==6 else ''}: {len(sh)} shadowing multisets")
    if not sh: continue
    always=set(pool)
    for ms in sh: always &= set(ms)
    print(f"  present in EVERY one: {sorted(label(m) for m in always)}")
    c=Counter(m for ms in sh for m in set(ms))
    print(f"  most common movers: {[(label(m),n) for m,n in c.most_common(8)]}")
    qs=Counter(q for ms in sh for _,q in ms)
    print(f"  denominators used: {dict(sorted(qs.items()))}")
    for ms in sh[:6]: print(f"     {[label(m) for m in ms]}")
