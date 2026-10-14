from fractions import Fraction as F
from itertools import combinations
from math import gcd
TH = F(1,8)
def cd(x):
    f = x % 1; return min(f,1-f)
def blocks(r,k): return cd(r*(k+TH)) < TH
def lcm(xs):
    l=1
    for x in xs: l=l*x//gcd(l,x)
    return l
def minimal_covers(c):
    cands = sorted({F(a,c) for a in range(1,c)})
    out=[]
    for size in range(1,7):
        for sub in combinations(cands,size):
            L=lcm([r.denominator for r in sub])
            if not all(any(blocks(r,k) for r in sub) for k in range(L)): continue
            if any(s and all(any(blocks(r,k) for r in s) for k in range(lcm([r.denominator for r in s])))
                   for s in (sub[:i]+sub[i+1:] for i in range(size))): continue
            out.append(sub)
        if out: return out
    return out
print("For each minimal largest-flank cover: does SOME OTHER flank have an uncovered residue class?")
print("(that is the eighth-family mechanism: a free flank the sixth difference can be cleared on)\n")
for c in (8,10,12,16):
    covs = minimal_covers(c)
    print(f"=== d_max = c = {c}: {len(covs)} minimal cover(s) ===")
    for cov in covs:
        D = sorted(int(c*r) for r in cov) + [c]      # the fixed differences, incl. the flank itself
        report=[]
        for e in D:
            if e == 0: continue
            others = [d for d in D if d != e]
            ratios = [F(d,e) for d in others]
            L = lcm([r.denominator for r in ratios])
            free = [k for k in range(L) if not any(blocks(r,k) for r in ratios)]
            if free: report.append((e, L, free[:4], len(free)))
        tag = "  <- eighth pattern" if sorted(cov)==sorted([F(1,8),F(3,8),F(1,2),F(5,8),F(7,8)]) else ""
        print(f"  fixed differences {D}{tag}")
        if report:
            for e,L,fr,n in report:
                print(f"     flank {e:3}: {n} uncovered residue(s) mod {L}, e.g. k = {fr}")
        else:
            print("     NO flank has an uncovered residue class  <-- every flank shadowed by the fixed set")
    print()
