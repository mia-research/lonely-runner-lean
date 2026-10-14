"""The reduced question.  At a resonant flank e = n f, A is cleared by any a solving the
sub-problem for A/n at flank f; a is then pinned only mod n*f, leaving n lifts.
QUESTION: does some lift clear B?  Measured, then range-tested immediately."""
from math import gcd
from itertools import combinations
import random
N=8
def clear(d,e,a,n=N): return e<=(d*a)%(n*e)<=(n-1)*e
def sub_solutions(Ared,f,n=N):
    """a mod n*f with a = 1 mod n clearing every m' in Ared at flank f"""
    return [a for a in range(1,n*f,1) if a%n==1 and all(clear(m,f,a) for m in Ared if m!=f)]
def descent_works(L,n=N):
    """is there a resonant flank e=n f and a lift of a sub-solution clearing B?"""
    A=[d for d in L if d%n==0]; B=[d for d in L if d%n]
    for e in A:
        f=e//n
        if f==0: continue
        Ared=[d//n for d in A]
        for a0 in sub_solutions(Ared,f,n):
            for t in range(n):
                a=a0+t*n*f
                if a%(n*e)==0: continue
                if all(clear(b,e,a) for b in B): return True,(e,a)
    return False,None
def middle(L,n=N):
    M=sum(1 for d in L if d%n==0); return 1<=M<=len(L)-2

print("=== how many of the n lifts clear B, and does one always? ===")
random.seed(31415)
import collections
print("  range   middle sets   descent closes   FAILS   mean surviving lifts (of 8)")
for H in (28,45,70,110,170):
    t=ok=0; surv=[]; fails=[]
    tries=0
    while t<900 and tries<400000:
        tries+=1
        L=sorted(random.sample(range(1,H+1),7))
        if L[0]!=1: L[0]=1; L=sorted(set(L))
        if len(L)!=7 or not middle(L): continue
        t+=1
        w,wit=descent_works(L)
        if w: ok+=1
        else:
            fails.append(tuple(L))
        # count surviving lifts at the first resonant flank with a sub-solution
        A=[d for d in L if d%N==0]; B=[d for d in L if d%N]
        for e in A:
            f=e//N
            if f==0: continue
            ss=sub_solutions([d//N for d in A],f)
            if ss:
                a0=ss[0]
                surv.append(sum(1 for tt in range(N) if all(clear(b,e,a0+tt*N*f) for b in B)))
                break
    m=sum(surv)/len(surv) if surv else float('nan')
    print(f"  [1,{H:3d}] {t:12d} {ok:15d} {t-ok:7d}   {m:.2f}")
    if fails[:2]: print(f"           failures e.g. {fails[:2]}")
