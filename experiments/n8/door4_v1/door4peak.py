# EXHAUSTIVE over the binding region: all 7-subsets of distinct positive integers with
# sum(ds) <= 80.  Find the true worst error/M and the true smallest cushion (M-1)/error.
from math import gcd
from itertools import combinations
def win(a,b):
    s=a%8; lo=-(-(b-s)//8); hi=(7*b-s)//8
    return hi-lo+1
def exact_main(ds):
    t=0.0
    for b in ds:
        x=float(b)
        for a in ds:
            if a!=b: x *= win(a,b)/b
        t+=x
    return t
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def T(ds): return sum(sum(1 for k in range(b) if all(clear(a,b,k) for a in ds)) for b in ds)
SMAX=80
best_e=None; best_cush=None; minT=None; n=0
# generate 7-subsets with bounded sum
def gen(pref, start, rem):
    global n, best_e, best_cush, minT
    if len(pref)==7:
        if rem<0: return
        ds=tuple(pref)
        if gcd(*ds)!=1: return
        n+=1
        M=exact_main(ds); t=T(ds); e=(M-t)/M
        if best_e is None or e>best_e[0]: best_e=(e,ds,t,M)
        cush=(M-1)/(M-t) if M>t else 9e9
        if best_cush is None or cush<best_cush[0]: best_cush=(cush,ds,t,M)
        if minT is None or t<minT[0]: minT=(t,ds,M)
        return
    need=7-len(pref)
    # minimal completion from `start`
    for v in range(start, SMAX+1):
        mincomp=sum(range(v, v+need))
        if mincomp>rem: break
        gen(pref+[v], v+1, rem-v)
gen([],1,SMAX)
print(f"EXHAUSTIVE over all primitive 7-subsets with sum(ds) <= {SMAX}:  {n} sets")
print(f"  worst error/M   : {best_e[0]:.4f} at ds={best_e[1]}  (T={best_e[2]}, M={best_e[3]:.3f}, need < {1-1/best_e[3]:.4f})")
print(f"  smallest cushion: {best_cush[0]:.4f}x at ds={best_cush[1]}  (T={best_cush[2]}, M={best_cush[3]:.3f})")
print(f"  minimum T       : {minT[0]} at ds={minT[1]} (M={minT[2]:.3f})")
print()
print(f"  sets with T = 0 : {'NONE' if minT[0]>0 else 'FOUND'}")
print(f"  the first-moment argument SUCCEEDS on every one of these {n} sets: "
      f"{'YES' if best_cush[0]>1 else 'NO'}")
