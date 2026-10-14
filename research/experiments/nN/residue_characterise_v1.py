"""Item 3: characterise the residue -- the sets on which DIV, SELF and BAND all fail.

FIRST, the control on the signature I floated last turn ("every survivor starts 1,2,3").
Features are fixed BEFORE looking at the split, and each is reported against the matched
baseline: the DIV-failing population, which is the only population survivors are drawn from.

Note what carries no information: survivors fail DIV, so by ratWorks_family_fails_iff they
cover every modulus in [2,n] by divisibility.  That is FORCED and is not a finding.
"""
from itertools import combinations
from fractions import Fraction as F
import math, collections
def DIV(ds,n):
    for q in range(2,n+1):
        if all(d%q for d in ds): return True
    return False
def SELF(ds,n):
    return any(all(d%n==0 for d in ds if d!=e) for e in ds)
def BAND(ds,n,KMAX=60,MMAX=60):
    for e in ds:
        rest=[d for d in ds if d!=e]
        if not rest: return True
        lo,hi=min(rest),max(rest)
        for k in range(KMAX):
            T=n*k+1
            if (hi-lo)*T > e*(n-2): break
            for M in range(MMAX):
                if e*(n*M+1)<=lo*T and hi*T<=e*(n*M+n-1): return True
    return False
for n,HI in ((5,26),(6,20),(7,15),(8,13)):
    k=n-1
    surv=[]; divfail=[]
    for c in combinations(range(1,HI+1),k):
        g=c[0]
        for x in c[1:]: g=math.gcd(g,x)
        if g!=1: continue
        if DIV(c,n): continue
        divfail.append(c)
        if not SELF(c,n) and not BAND(c,n): surv.append(c)
    def share(pop, f): return sum(1 for c in pop if f(c))
    feats = {
      "starts 1,2,3"      : lambda c: c[:3]==(1,2,3),
      "contains 1"        : lambda c: 1 in c,
      "d_max/d_min > n-1" : lambda c: c[-1] > (n-1)*c[0],
      "d_max/d_min > 2n"  : lambda c: c[-1] > 2*n*c[0],
    }
    print(f"n={n}   DIV-failing population {len(divfail)}   survivors {len(surv)}")
    for name,f in feats.items():
        b=share(divfail,f); s=share(surv,f)
        rb=b/len(divfail) if divfail else 0; rs=s/len(surv) if surv else 0
        ratio=(rs/rb) if rb>0 else float('nan')
        print(f"   {name:<20} baseline {b:>6}/{len(divfail):<6} ({100*rb:5.1f}%)"
              f"   survivors {s:>5}/{len(surv):<5} ({100*rs:5.1f}%)   x{ratio:.2f}")
    print()
