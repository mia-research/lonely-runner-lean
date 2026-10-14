from itertools import combinations
from math import gcd
from functools import reduce
import collections
def nopen(ds,e):
    "exact number of surviving openings at flank e"
    M=8*e; r=[d%M for d in ds]; st=[(8*d)%M for d in ds]; c=0
    for _ in range(e):
        if all(e<=x<=7*e for x in r): c+=1
        for i in range(7): r[i]=(r[i]+st[i])%M
    return c
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def omega(n):
    s=0; p=2; m=n
    while p*p<=m:
        if m%p==0:
            s+=1
            while m%p==0: m//=p
        p+=1
    if m>1: s+=1
    return s

H=30
byprime={True:[0,0],False:[0,0]}        # [sets, failures]
bymin=collections.defaultdict(lambda:[0,0])
byomega=collections.defaultdict(lambda:[0,0])
surv=collections.defaultdict(list)
for c in combinations(range(1,H+1),7):
    if reduce(gcd,c)!=1: continue
    e=c[-1]; cnt=nopen(c,e); f=(cnt==0)
    p=isprime(e)
    byprime[p][0]+=1; byprime[p][1]+=f
    mn=min(e//gcd(d,e) for d in c if d!=e)
    bymin[mn][0]+=1; bymin[mn][1]+=f
    w=omega(e)
    byomega[w][0]+=1; byomega[w][1]+=f
    surv[p].append(cnt)

print(f"WHY THE LARGEST FLANK FAILS  (exhaustive primitive 7-subsets of [1,{H}])\n")
print("1) is d_max PRIME?")
for p in (True,False):
    n,f=byprime[p]; print(f"   prime={str(p):5s}: {f:5d} failures / {n:8d} sets = {100*f/n:.4f}%")
r=(byprime[False][1]/byprime[False][0])/(byprime[True][1]/byprime[True][0])
print(f"   -> composite flank fails {r:.1f}x more often than prime\n")

print("2) number of distinct primes of d_max")
print(f"   {'omega':>6} {'sets':>9} {'fail':>7} {'rate %':>9}")
for w in sorted(byomega):
    n,f=byomega[w]; print(f"   {w:>6} {n:>9} {f:>7} {100*f/n:>9.4f}")

print("\n3) the smallest CRT modulus c_d = d_max/gcd(d,d_max) over the other six")
print("   (c_d = 2 means one disparity constrains k only mod 2 -- a coarse, correlated cut)")
print(f"   {'min c_d':>8} {'sets':>9} {'fail':>7} {'rate %':>9}")
for m in sorted(bymin)[:12]:
    n,f=bymin[m]; print(f"   {m:>8} {n:>9} {f:>7} {100*f/n:>9.4f}")

import statistics as st
print("\n4) surviving openings at d_max (the quantity that hits 0)")
for p in (True,False):
    v=surv[p]; print(f"   d_max {'prime    ' if p else 'composite'}: mean {st.mean(v):6.2f}  median {st.median(v):5.1f}  min {min(v)}")
print("\n   WITHDRAWN 2026-09-20: an earlier version of this file explained the table by")
print("   'each constraint removes about a quarter, so survivors ~ e*(3/4)^6'. That is an")
print("   independent-density estimate. It is banned by MANUSCRIPT §6A row six, and it is")
print("   also REFUTED -- Appendix A routes 10-14 measured the joint density BELOW the")
print("   product of the pairwise conditionals (ratio to 0.716, 2594/3000 profiles), so the")
print("   constraints anti-correlate and the estimate is wrong as well as inadmissible.")
print("")
print("   What stands, exactly and without density:")
print("     * flank e has exactly e openings                     (Theorem 15H)")
print("     * for d < e,  c_d = e/gcd(d,e) = m  <=>  d = j*e/m, gcd(j,m)=1;")
print("       in particular  c_d = 2  <=>  e/2 is itself a disparity   (checked, 0 mismatches)")
print("     * a witness at e exists iff the CRT system {k mod c_d in A_d} is solvable")
print("   The table above is a MEASUREMENT of association between min c_d and failure.")
print("   It is not an explanation, and nothing here derives the failure rate.")
