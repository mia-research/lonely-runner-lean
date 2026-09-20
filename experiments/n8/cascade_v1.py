"""AP -> grid -> enlarged step.  Descriptive pass (PREREG_DSWEEP_v1 section 2.3 only).
DEVIATIONS FROM PREREG v1: no primary statistic, no surrogate arm, no p-values.
Characterisation block only, decided before the run.  Integer arithmetic throughout."""
import random
from math import gcd
from functools import reduce
from collections import Counter

def clear(V,i,D):
    for p in (1,3,5,7):
        if all(D <= (p*abs(V[i]-V[j])) % (8*D) <= 7*D for j in range(8) if j!=i):
            return p
    return None

def cascade(V,i):
    g = reduce(gcd,[abs(V[a]-V[b]) for a in range(8) for b in range(a+1,8)])
    m = min(abs(V[i]-V[j]) for j in range(8) if j!=i)
    if clear(V,i,g)     is not None: return ('AP', g, m, g)
    if clear(V,i,m)     is not None: return ('grid', m, m, g)
    for D in range(1, 7*m+1):
        if clear(V,i,D) is not None: return ('enlarged', D, m, g)
    return ('none', None, m, g)

random.seed(20)
pops = [('random [0,10^3)',10**3),('random [0,10^5)',10**5),('random [0,10^7)',10**7)]
for lab,N in pops:
    tier=Counter(); Ds=[]
    for _ in range(1500):
        V=sorted(random.sample(range(0,N),8))
        for i in range(8):
            t,D,m,g = cascade(V,i)
            tier[t]+=1
            if t=='enlarged': Ds.append((D,m,g,V[-1]-V[0]))
    n=sum(tier.values())
    print('%-18s runners %5d   AP %5.1f%%   grid %5.1f%%   enlarged %5.1f%%   none %5.2f%%'
          %(lab,n,100*tier['AP']/n,100*tier['grid']/n,100*tier['enlarged']/n,100*tier['none']/n))
    if Ds:
        print('      enlarged cases: %d.  D/d_min:'%len(Ds), Counter(round(D/m,1) for D,m,g,s in Ds).most_common(6))
        print('      D itself      :', Counter(D for D,m,g,s in Ds).most_common(8))
        print('      D divides span:', sum(1 for D,m,g,s in Ds if s%D==0),'/',len(Ds),
              '   D multiple of g:', sum(1 for D,m,g,s in Ds if D%g==0),'/',len(Ds))
        print('      7D/span       :', Counter(round(7*D/s,1) for D,m,g,s in Ds).most_common(6))
    print()
