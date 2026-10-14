"""The shadowing count as a RULE.  Flank e is ours to choose, so the criterion is
      EXISTS e in ds :  sum_{d != e} c_d * gcd(d,e)  <  e
which by Theorem 15.50 (contrapositive) forces a clear opening, hence loneliness.
Everything here is exact integer arithmetic."""
from math import gcd
from itertools import combinations

def blocked_classes(d,e,n=8):
    """c_d = # blocked residue classes mod q, q = e/gcd(d,e).  Exact."""
    g=gcd(d,e); q=e//g
    return sum(1 for j in range(q) if not (e <= (d*(n*j+1)) % (n*e) <= (n-1)*e))

def count_at(ds,e,n=8):
    return sum(blocked_classes(d,e,n)*gcd(d,e) for d in ds if d!=e)

def rule_fires(ds,n=8):
    """returns the flank with the smallest count, and whether the rule fires there"""
    best=None
    for e in ds:
        c=count_at(ds,e,n)
        if best is None or c*best[1]<best[0]*e: pass
        if best is None or (c/e)<(best[0]/best[1]): best=(c,e)
    return best[0]<best[1], best          # (fires?, (count, e))

def clear_opening(ds,e,n=8):
    for j in range(e):
        if all(e<=(d*(n*j+1))%(n*e)<=(n-1)*e for d in ds): return j
    return None

if __name__=="__main__":
    print("=== 0. the zero-contribution fact, checked ===")
    # if e | d and 8 does not divide d/e, then d blocks NO opening
    bad=[]
    for e in range(1,40):
        for m in range(1,30):
            d=e*m
            c=blocked_classes(d,e)
            expect = 1 if m%8==0 else 0
            if c!=expect: bad.append((e,m,c,expect))
    print("   e|d, 8∤(d/e)  =>  c_d = 0 (never blocks);  8|(d/e) => c_d = 1 (blocks all)")
    print("   violations:",len(bad))

    print()
    print("=== 1. soundness: does the rule firing imply a clear opening? ===")
    bad=[];fired=0
    for ds in combinations(range(1,22),7):
        if ds[0]!=1: continue
        f,(c,e)=rule_fires(list(ds))
        if f:
            fired+=1
            if clear_opening(list(ds),e) is None: bad.append((ds,e,c))
    print(f"   fired on {fired} sets; unsound cases: {len(bad)}")

    print()
    print("=== 2. reach on the MIDDLE of the trichotomy, order 8 (c=7, 1<=M<=5) ===")
    tot=mid=hit=0; misses=[]
    for ds in combinations(range(1,22),7):
        if ds[0]!=1: continue
        tot+=1
        M=sum(1 for d in ds if d%8==0)
        if not (1<=M<=len(ds)-2): continue
        mid+=1
        f,(c,e)=rule_fires(list(ds))
        if f: hit+=1
        elif len(misses)<6: misses.append((ds,c,e,round(c/e,3)))
    print(f"   sets scanned {tot}; in the middle {mid}; count rule fires on {hit}")
    print(f"   best ratio on a sample of misses (count/e, needs < 1):")
    for m in misses: print("     ",m)
