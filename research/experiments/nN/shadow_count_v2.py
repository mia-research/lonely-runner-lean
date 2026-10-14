"""Where the count rule bites in the middle of the trichotomy, and what it adds to R1-R7."""
from math import gcd
from itertools import combinations
N=8
def c_of(d,e,n=N):
    g=gcd(d,e); q=e//g
    return sum(1 for j in range(q) if not (e<=(d*(n*j+1))%(n*e)<=(n-1)*e))
def count_at(ds,e,n=N): return sum(c_of(d,e,n)*gcd(d,e) for d in ds if d!=e)
def best_flank(ds,n=N):
    return min(((count_at(ds,e,n),e) for e in ds), key=lambda t:(t[0]/t[1],t[1]))
def clear_opening(ds,e,n=N):
    for j in range(e):
        if all(e<=(d*(n*j+1))%(n*e)<=(n-1)*e for d in ds): return j
    return None
# existing rules
def R1(ds,n=N): return max(ds)<=(n-1)*min(ds)
def R6(ds,n=N): return any(all(d%q for d in ds) for q in range(2,n+1))
def R4(ds,n=N):
    if n not in (2,3,5,7,11,13): return False
    mult=[d for d in ds if d%n==0]
    return len(mult)==1 and max(ds)%n==0
def R5(ds,n=N):
    return sum(1 for d in ds if d%n!=0)<=1

print("=== A. the e=1 flank IS the trichotomy's left end ===")
bad=0
for ds in combinations(range(1,20),7):
    if ds[0]!=1: continue
    M=sum(1 for d in ds if d%N==0)
    if count_at(list(ds),1)!=M: bad+=1
print("   count at flank e=1 equals M = #{d : 8|d}  -- violations:",bad)
print("   so 'count < e' at e=1 reads M < 1, i.e. M = 0: exactly the closed left end.")
print("   In the middle M>=1, so the e=1 flank ALWAYS just fails. A larger flank is required.")

print()
print("=== B. reach in the middle, and what it ADDS ===")
mid=0; fires=0; addl=0; unreached=0; ex=[]
for ds in combinations(range(1,22),7):
    if ds[0]!=1: continue
    L=list(ds); M=sum(1 for d in L if d%N==0)
    if not (1<=M<=len(L)-2): continue
    mid+=1
    f = count_at(L,best_flank(L)[1]) < best_flank(L)[1]
    old = R1(L) or R6(L) or R4(L) or R5(L)
    if f: fires+=1
    if f and not old: addl+=1
    if not f and not old:
        unreached+=1
        if len(ex)<8: ex.append((ds,M,best_flank(L)))
print(f"   middle sets            : {mid}")
print(f"   count rule fires       : {fires}")
print(f"   of which NOT reached by R1/R4/R5/R6 : {addl}   <-- genuinely new")
print(f"   reached by neither     : {unreached}")

print()
print("=== C. the ratio min(count/e) on middle sets ===")
import collections
h=collections.Counter()
for ds in combinations(range(1,20),7):
    if ds[0]!=1: continue
    L=list(ds); M=sum(1 for d in L if d%N==0)
    if not (1<=M<=len(L)-2): continue
    c,e=best_flank(L); h[round(c/e,1)]+=1
for k in sorted(h): print(f"     ratio ~{k:4}  {h[k]}")

print()
print("=== D. sets reached by nothing: what do they look like ===")
for ds,M,(c,e) in ex: print(f"     {ds}  M={M}  best flank e={e}, count={c}, ratio={c/e:.2f}")
