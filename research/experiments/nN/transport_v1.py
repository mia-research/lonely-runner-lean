"""Does the AP's reading SURVIVE transport under deformation?
For each subject: the AP's isolation set, the deformed one, and whether they overlap.
If they overlap, the phi(n) law's reading is carried to the deformed arrangement."""
from fractions import Fraction as F
def ivs(ds,U):
    out=None
    for d in ds:
        bl=[];k=0
        while F(8*k+1,1)/d<=U:
            a=F(8*k+1)/d;b=F(8*k+7)/d
            bl.append((max(a,F(0)),min(b,U)));k+=1
        bl=[(a,b) for a,b in bl if b>a]
        out=bl if out is None else [(max(a,c),min(b,e)) for a,b in out for c,e in bl if min(b,e)>max(a,c)]
    return out or []
def meas(x): return sum(b-a for a,b in x)
def overlap(A,B): return meas([(max(a,c),min(b,d)) for a,b in A for c,d in B if min(b,d)>max(a,c)])
U=F(20)
AP=[F(i) for i in range(8)]
base=[ivs([abs(v-w) for w in AP if w!=v],U) for v in AP]
print("  subject:            0      1      2      3      4      5      6      7")
print(f"  AP |L|:        {'  '.join(f'{float(meas(b)):5.2f}' for b in base)}")
for num in (1,10,50,200,600):
    e=F(num,1000)
    V=[F(i) for i in range(7)]+[F(7)+e]
    cur=[ivs([abs(v-w) for w in V if w!=v],U) for v in V]
    ov=[overlap(base[k],cur[k]) for k in range(8)]
    print(f"  e={str(e):7s} overlap {'  '.join(f'{float(o):5.2f}' for o in ov)}")
    print(f"  {'':15s}|L| {'  '.join(f'{float(meas(c)):5.2f}' for c in cur)}")
print()
print("  overlap = measure of AP-set INTERSECT deformed-set.  Non-zero means the AP's own")
print("  reading is still a reading of the deformed arrangement: the reading is TRANSPORTED.")
