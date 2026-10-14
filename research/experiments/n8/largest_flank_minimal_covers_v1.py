from fractions import Fraction as F
from itertools import combinations
TH = F(1,8)
def cd(x):
    f = x % 1; return min(f, 1-f)
def blocks(r,k): return cd(r*(k+TH)) < TH
def shadows(sub, L):
    return all(any(blocks(r,k) for r in sub) for k in range(L))
def lcm(xs):
    from math import gcd
    l=1
    for x in xs: l = l*x//gcd(l,x)
    return l
print("minimal shadowing covers (any size) by ratios in (0,1) with denominator dividing c")
print("a cover is MINIMAL when no proper subset shadows\n")
for c in (4,5,6,7,8,9,10,11,12,16):
    cands = sorted({F(a,c) for a in range(1,c)})
    mins = []
    for size in range(1,7):
        for sub in combinations(cands,size):
            L = lcm([r.denominator for r in sub])
            if not shadows(sub,L): continue
            # minimal?
            red = False
            for drop in range(size):
                s2 = sub[:drop]+sub[drop+1:]
                if s2 and shadows(s2, lcm([r.denominator for r in s2])): red=True; break
            if not red: mins.append(sub)
        if mins: break     # smallest size only
    if mins:
        sz = len(mins[0])
        print(f"c={c:2}: minimal covers have size {sz}; count {len(mins)}")
        for s in mins[:6]: print(f"        {[str(x) for x in s]}")
        if len(mins)>6: print(f"        ... {len(mins)-6} more")
    else:
        print(f"c={c:2}: no shadowing cover of size <= 6")
    print()
