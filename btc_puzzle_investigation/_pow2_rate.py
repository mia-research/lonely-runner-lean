import csv, random
rnd=random.Random(1)
def d_recursion(N,e):
    s=[]; e=abs(e)
    while e>0:
        D=N//e
        if D==0: break
        s.append(D); e=abs(e-N//D)
    return s
def is_pow2(x): return x>0 and (x&(x-1))==0
def ends_pow2(N,d): 
    s=d_recursion(N,d); return is_pow2(s[-1]) if s else False
rows=sorted([(int(r["bits"]),int(r["private_key"],16),r["puzzle"]) for r in csv.DictReader(open("puzzles_verified.csv"))])
rows=[(P,d,pz) for P,d,pz in rows]

real_hits=[(pz,P) for P,d,pz in rows if ends_pow2(1<<P,d)]
print(f"REAL keys ending in power-of-2: {len(real_hits)}/{len(rows)}")
print(f"  which: {[f'pz{pz}(P{P})' for pz,P in real_hits]}")

# matched random baseline (same P's), rate
trials=2000
cnt=0; tot=0
for _ in range(trials):
    for P,_,_ in rows:
        d=(1<<(P-1))+rnd.randrange(1<<(P-1))
        tot+=1; cnt+=ends_pow2(1<<P,d)
print(f"\nRANDOM baseline rate: {cnt/tot:.3f}  => expected {cnt/tot*len(rows):.1f} of {len(rows)} keys")
print(f"REAL rate: {len(real_hits)/len(rows):.3f}")

# is the LAST error hitting exactly 1 (=> last term = N = 2^P) the common case?
from collections import Counter
lastvals=Counter()
for P,d,pz in rows:
    s=d_recursion(1<<P,d)
    if is_pow2(s[-1]):
        lastvals[P-(s[-1].bit_length()-1)]+=1   # P - log2(lastD) = log2(e_last)
print(f"\nfor power-of-2 enders, log2(final error e_last) dist: {dict(sorted(lastvals.items()))}  (0 => e_last=1)")
