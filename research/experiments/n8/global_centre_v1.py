"""|S| >= 2 beyond the 34%.
Clear window at modulus b: r in [L,U], L = ceil((b-1)/8), U = floor((7b-1)/8).
A reflection r -> c - r preserves [L,U] exactly when c = L+U.  Compute L+U:
   b % 8 in [2,7]  ->  c = b     (centre 0 mod b)
   b % 8 in {0,1}  ->  c = b-1   (centre -1 mod b)
A GLOBAL reflection q -> C - q therefore needs C = 0 (mod b) at good moduli and C = -1 (mod b)
at obstructed ones -- solvable by CRT iff every good modulus is coprime to every obstructed one."""
from math import gcd, lcm
from functools import reduce
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def good(b): return 2 <= b % 8 <= 7
print("(1) c = L+U per residue class of b mod 8:")
for b in range(2,26):
    c=L(b)+U(b)
    print(f"   b={b:2d} (b%8={b%8})  L={L(b):2d} U={U(b):2d}  c=L+U={c:2d}  "
          f"{'= b     (centre 0)' if c==b else '= b-1   (centre -1)' if c==b-1 else 'OTHER'}"
          f"   clear residues: {U(b)-L(b)+1}")
def crt_centre(bs):
    """smallest C >= 0 with C = 0 mod b (good) / -1 mod b (obstructed), or None"""
    M=reduce(lcm,bs)
    for C in range(M):
        if all((C % b == 0) if good(b) else (C % b == b-1) for b in bs): return C
    return None
def S_of(bs):
    M=reduce(lcm,bs)
    return [q for q in range(M) if all(L(b) <= q % b <= U(b) for b in bs)]
random.seed(4)
print("\n(2) over random 5-modulus profiles, all b_i dividing a common m:")
allgood=cent=n=0; minS=99; singleton=[]
for _ in range(4000):
    m=random.choice([24,36,48,60,72,96,120,144,180,240,360])
    divs=[d for d in range(2,m+1) if m%d==0]
    if len(divs)<5: continue
    bs=sorted(random.sample(divs,5))
    if reduce(lcm,bs)>200000: continue
    n+=1
    if all(good(b) for b in bs): allgood+=1
    if crt_centre(bs) is not None: cent+=1
    S=S_of(bs); minS=min(minS,len(S))
    if len(S)==1: singleton.append(bs)
print(f"   profiles: {n}")
print(f"   all moduli good (the PROVED 34% case): {100*allgood/n:.1f}%")
print(f"   a global CRT centre exists:            {100*cent/n:.1f}%")
print(f"   minimum |S| seen: {minS};  singletons: {len(singleton)} {singleton[:3]}")
