import csv
from math import gcd, log2
def d_recursion(N,e):
    s=[]; e=abs(e)
    while e>0:
        D=N//e
        if D==0: break
        s.append(D); e=abs(e-N//D)
    return s
def is_pow2(x): return x>0 and (x&(x-1))==0
rows=sorted([(int(r["bits"]),int(r["private_key"],16),r["puzzle"]) for r in csv.DictReader(open("puzzles_verified.csv"))])

print("CLEAN offset cases (offset = d - 2^(P-1); short signature = few/no error terms):")
for P,d,pz in rows:
    off=d-(1<<(P-1))
    if off<=0:
        print(f"  pz{pz:>3} P={P:>3} d={d:<6} offset=0                       -> EXACT half (d = 2^(P-1))")
        continue
    sig=d_recursion(1<<(P-1),off)
    if len(sig)<=2:
        note=""
        for t in sig:
            if is_pow2(t): note+=f" [{t}=2^{int(log2(t))}]"
        print(f"  pz{pz:>3} P={P:>3} d={d:<8} offset={off:<8} sig={sig}{note}")

print("\nFULL-key signatures ending in an exact power of 2 (error collapsed to 1 or 2):")
for P,d,pz in rows:
    sig=d_recursion(1<<P,d)
    if is_pow2(sig[-1]):
        print(f"  pz{pz:>3} P={P:>3}  last D={sig[-1]}=2^{int(log2(sig[-1]))}  (N=2^{P})  full={sig}")

print("\nposition d/2^P — numerator factorization (small clean keys):")
for P,d,pz in rows:
    if P>16: break
    from fractions import Fraction
    fr=Fraction(d,1<<P); num=fr.numerator
    f={}; x=num; p=2
    while p*p<=x:
        while x%p==0: f[p]=f.get(p,0)+1; x//=p
        p+=1
    if x>1: f[x]=f.get(x,0)+1
    print(f"  pz{pz:>3} P={P:>2} d={d:<6} = {fr}   numerator {num} = {f}")
