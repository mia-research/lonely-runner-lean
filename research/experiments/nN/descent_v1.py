"""Which flank can carry a descent on the middle of the trichotomy.
Structural questions only -- no coverage counts are reported as progress."""
from math import gcd
from itertools import combinations
import random
N=8
def clear_at(ds,e,k,n=N):
    a=n*k+1
    return all(e<=(d*a)%(n*e)<=(n-1)*e for d in ds)
def clear_flanks(ds,n=N):
    """which flanks have SOME clear opening"""
    out={}
    for e in ds:
        ks=[k for k in range(e) if clear_at(ds,e,k,n)]
        if ks: out[e]=ks
    return out
def middle(L,n=N):
    M=sum(1 for d in L if d%n==0); return 1<=M<=len(L)-2

random.seed(11)
print("=== Q1. in the middle, is a NON-RESONANT flank (gcd(e,n)=1) always clear somewhere? ===")
print("    also: a resonant flank?  a flank in B (n dnd e)?  a flank in A (n | e)?")
tot=0; noNR=0; noA=0; noB=0; noRes=0
ex=[]
for H in (14,20,28):
    t=nr=aa=bb=rr=0
    for L in combinations(range(1,H+1),7):
        if L[0]!=1 or not middle(L): continue
        L=list(L); t+=1
        cf=clear_flanks(L)
        A=[d for d in L if d%N==0]; B=[d for d in L if d%N]
        if not any(gcd(e,N)==1 for e in cf): nr+=1
        if not any(gcd(e,N)>1 for e in cf): rr+=1
        if A and not any(e in cf for e in A): aa+=1
        if B and not any(e in cf for e in B): bb+=1
        if not any(gcd(e,N)==1 for e in cf) and len(ex)<4: ex.append((tuple(L),sorted(cf)))
    print(f"    [1,{H:2d}] middle={t:6d}   no clear NON-RESONANT flank: {nr:5d}   no clear resonant flank: {rr:5d}"
          f"   no clear flank in A: {aa:5d}   none in B: {bb:5d}")
print("    witnesses with no clear non-resonant flank:")
for w in ex: print("      ",w)

print()
print("=== Q2. THE DESCENT.  At a flank e, split the conditions. ===")
print("    resonant d = n*m'  :  (m'*a mod e) in the band at modulus e   -- depends on a mod e only")
print("    non-resonant d     :  needs a mod n*e")
print("    Question: when gcd(e,n)=1, a is DETERMINED by rho = a mod e (CRT, a = 1 mod n).")
bad=0;tot=0
for e in range(1,40):
    if gcd(e,N)!=1: continue
    seen={}
    for k in range(e):
        a=N*k+1; r=a%e
        tot+=1
        if r in seen and seen[r]!=a%(N*e): bad+=1
        seen[r]=a%(N*e)
    if len(seen)!=e: bad+=1
print(f"    checked {tot} openings at non-resonant flanks: rho -> a mod n*e is a bijection.  failures: {bad}")
