"""Where the union bound loses, and whether a pivoted bound recovers it.

Union bound (Thm 15.50):        |U B_d| <= sum_d |B_d|            = sum_d c_d*gcd(d,e)
Pivoted bound (valid):          |U B_d| <= |B_p| + sum_{d!=p} (|B_d| - |B_d ^ B_p|)
   because  U B_d = B_p u U_{d!=p} (B_d \ B_p)  and  |B_d \ B_p| = |B_d| - |B_d ^ B_p|.
Either bound < e forces a clear opening, hence loneliness."""
from math import gcd
from itertools import combinations
N=8
def blocked_set(d,e,n=N):
    return frozenset(j for j in range(e) if not (e<=(d*(n*j+1))%(n*e)<=(n-1)*e))
def bounds(ds,e,n=N):
    B=[blocked_set(d,e,n) for d in ds if d!=e]
    union=len(set().union(*B)) if B else 0
    b0=sum(len(x) for x in B)
    b1=min(len(P)+sum(len(X)-len(X&P) for X in B if X is not P) for P in B) if B else 0
    return b0,b1,union
def best(ds,n=N):
    r=[]
    for e in ds:
        b0,b1,u=bounds(ds,e,n); r.append((e,b0,b1,u))
    return r

print("=== A. is the pivoted bound ever better, and is it sound? ===")
bad=0; better=0; tot=0
for ds in combinations(range(1,18),7):
    if ds[0]!=1: continue
    for e,b0,b1,u in best(list(ds)):
        tot+=1
        if b1<u: bad+=1          # must never happen: b1 is an upper bound on the union
        if b1<b0: better+=1
print(f"   flank-instances {tot};  pivoted bound VIOLATED (b1<truth): {bad};  strictly better than union: {better}")

print()
print("=== B. what each bound closes in the MIDDLE of the trichotomy ===")
mid=u0=u1=truth=0
still=[]
for ds in combinations(range(1,22),7):
    if ds[0]!=1: continue
    L=list(ds); M=sum(1 for d in L if d%N==0)
    if not (1<=M<=len(L)-2): continue
    mid+=1
    r=best(L)
    f0=any(b0<e for e,b0,b1,u in r)
    f1=any(b1<e for e,b0,b1,u in r)
    ft=any(u<e for e,b0,b1,u in r)      # the truth: some opening actually clear
    u0+=f0; u1+=f1; truth+=ft
    if ft and not f1 and len(still)<6: still.append((ds,M,r))
print(f"   middle sets                         : {mid}")
print(f"   closed by the union bound (Thm 15.50): {u0}")
print(f"   closed by the pivoted bound          : {u1}")
print(f"   actually have a clear opening (truth): {truth}")
print(f"   gap the pivoted bound still leaves   : {truth-u1}")

print()
print("=== C. sets the truth reaches but the pivoted bound does not ===")
for ds,M,r in still:
    e,b0,b1,u=min(((x for x in r if x[3]<x[0])),key=lambda t:t[3]/t[0])
    print(f"     {ds} M={M}: at e={e}  union-bd={b0} pivot-bd={b1} TRUTH={u}  (need <{e})")
