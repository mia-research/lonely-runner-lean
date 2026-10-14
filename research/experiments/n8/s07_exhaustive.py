"""S07: EXHAUSTIVE over all admissible E with lcm(E)=L, for every L = 0 mod 8 up to LMAX.
Every e in E divides L, so enumerating 7-subsets of divisors(L) is complete.
Unit-complete forces R_non = {1,3,5,7,z}, z in {2,4,6}; |E_non| in {5,6}; |E_div| in {1,2}.
All arithmetic exact integer."""
import sys
from itertools import combinations, product
from math import gcd
from n8_fibre_core import L_of, split, safe, div_ok, witness_from_fibre

def divisors(n):
    d=[];i=1
    while i*i<=n:
        if n%i==0:
            d.append(i)
            if i!=n//i: d.append(n//i)
        i+=1
    return sorted(d)

def gen_E(L):
    D=divisors(L)
    Ddiv=[d for d in D if d%8==0]
    if not Ddiv: return
    cls={r:[d for d in D if d%8==r] for r in range(1,8)}
    for z in (2,4,6):
        if not cls[z]: continue
        classes=[1,3,5,7,z]
        if any(not cls[r] for r in classes): continue
        # |E_non|=5 : one per class, |E_div|=2
        for base in product(*[cls[r] for r in classes]):
            base=tuple(sorted(base))
            for dv in combinations(Ddiv,2):
                E=tuple(sorted(base+dv))
                if len(set(E))!=7: continue
                yield E
            # |E_non|=6 : one class doubled, |E_div|=1
            for dcls in classes:
                for extra in cls[dcls]:
                    if extra in base: continue
                    non=tuple(sorted(base+(extra,)))
                    for dv in Ddiv:
                        E=tuple(sorted(non+(dv,)))
                        if len(set(E))!=7: continue
                        yield E

def analyse(E,L):
    Ed,En=split(E)
    lo,hi=-(-L//8),(7*L)//8
    W=[(-(-2*L//7),(2*L)//5),(-(-3*L//5),(5*L)//7)]
    s_hon=s_hon_w=0; ex=None
    for b in range(lo,hi+1):
        if not div_ok(Ed,b,L): continue
        if not safe(En,b,L): continue
        s_hon+=1
        if any(a<=b<z for a,z in W):
            s_hon_w+=1
            if ex is None: ex=b
    return s_hon,s_hon_w,ex

LMAX=int(sys.argv[1]) if len(sys.argv)>1 else 1000
seen=set(); tot=0; failB=[]; failW=[]
for L in range(8,LMAX+1,8):
    for E in gen_E(L):
        if E in seen: continue
        if L_of(E)!=L: continue
        g=0
        for e in E: g=gcd(g,e)
        if g!=1: continue
        seen.add(E); tot+=1
        s,sw,ex=analyse(E,L)
        if s==0: failB.append((E,L))
        if sw==0: failW.append((E,L,s,len(split(E)[0])))
print(f"LMAX={LMAX}  admissible configurations (exhaustive): {tot}")
print(f"  NO safe fibre in B_hon at all : {len(failB)}")
print(f"  NO safe fibre in the 2 windows: {len(failW)}")
from collections import Counter
print("  window failures by |E_div|:", Counter(k for *_,k in failW))
for E,L,s,k in failW:
    Ed,En=split(E)
    print(f"    E={E} L={L} E_div={Ed} R_non={sorted(set(e%8 for e in En))} safe-in-B={s}")
for E,L in failB:
    print("    B-FAIL:",E,L)
