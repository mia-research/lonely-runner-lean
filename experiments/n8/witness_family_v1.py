from math import gcd
from itertools import combinations
def supp(ds):
    out={}
    for e in ds:
        ks=[k for k in range(e) if all(e<=(d*(8*k+1))%(8*e)<=7*e for d in ds)]
        if ks: out[e]=ks
    return out
def dead_by_intratio(ds):
    return {e:[d for d in ds if d%e==0 and (d//e)%8==0] for e in ds
            if any(d%e==0 and (d//e)%8==0 for d in ds)}

base=[2,3,4,5,6,7]
print("PATTERN from the exhaustive band: the only |S|=1 sets in [1,40] are")
print("  {2,3,4,5,6,7} + 16   and   {2,3,4,5,6,7} + 32   -- both powers of two >= 16.\n")
print("PREDICTION under test: {2,3,4,5,6,7} + 2^j has |S| = 1 for every j >= 4,")
print("with sole flank 2^j. Falsifier: any j >= 4 giving |S| != 1.\n")
print(f"  {'added x':>9} | {'|S|':>3} | supporting flanks | flanks dead by integer-ratio (8 | d/e)")
for x in [8,16,24,32,40,48,56,64,128,256,512,1024]:
    ds=sorted(base+[x])
    if len(set(ds))<7: print(f"  {x:>9} | (already in base)"); continue
    if gcd(gcd(gcd(ds[0],ds[1]),ds[2]),ds[3])!=1: pass
    S=supp(ds); D=dead_by_intratio(ds)
    mark=""
    if x&(x-1)==0 and x>=16: mark=("  <-- prediction: |S|=1 " + ("HOLDS" if len(S)==1 else "FAILS"))
    print(f"  {x:>9} | {len(S):>3} | {sorted(S)}   | {sorted(D)}{mark}")

print("\nWhy: the integer-ratio theorem kills flank e whenever some d in ds has e|d and 8|(d/e).")
for x in [16,32,64]:
    ds=sorted(base+[x]); D=dead_by_intratio(ds); S=supp(ds)
    alive=[e for e in ds if e not in D]
    print(f"  x={x:>4}: dead flanks {sorted(D)} ; alive {alive} ; actually supporting {sorted(S)}")

print("\nIs the base {2,3,4,5,6,7} itself special? same test with other 6-element bases:")
for b in [[1,2,3,4,5,6],[2,3,4,5,6,7],[3,4,5,6,7,8],[1,3,5,7,9,11],[2,3,5,7,11,13]]:
    row=[]
    for x in [16,32,64]:
        ds=sorted(b+[x])
        if len(set(ds))<7: row.append("dup"); continue
        row.append(str(len(supp(ds))))
    print(f"  base {str(b):22s} + [16,32,64] -> |S| = {row}")
