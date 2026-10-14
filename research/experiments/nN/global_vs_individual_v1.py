"""Fragility: does it kill INDIVIDUAL isolation, or only the COINCIDENCE of the eight?
Measure, exactly: each subject's own isolation set, and the global (all eight at once)."""
from fractions import Fraction as F
def clear_ivs(ds,U):
    ivs=None
    for d in ds:
        bl=[]; k=0
        while F(8*k+1,1)/d<=U:
            a=F(8*k+1)/d; b=F(8*k+7)/d
            bl.append((max(a,F(0)),min(b,U))); k+=1
        bl=[(a,b) for a,b in bl if b>a]
        ivs=bl if ivs is None else [(max(a,c),min(b,d2)) for a,b in ivs for c,d2 in bl if min(b,d2)>max(a,c)]
    return ivs or []
def meas(iv): return sum(b-a for a,b in iv)
def inter(A,B): return [(max(a,c),min(b,d)) for a,b in A for c,d in B if min(b,d)>max(a,c)]
U=F(4)
def report(V,label):
    V=sorted(V); subj=[]
    allset=None
    for k,v in enumerate(V):
        ds=[abs(v-w) for w in V if w!=v]
        iv=clear_ivs(ds,U); subj.append(meas(iv))
        allset=iv if allset is None else inter(allset,iv)
    print(f"  {label}")
    print(f"     per-subject isolation measure: {[round(float(x),6) for x in subj]}")
    print(f"     GLOBAL (all eight at once)   : {float(meas(allset)):.8f}   intervals {len(allset)}")
AP=[F(i) for i in range(8)]
report(AP,"AP  speeds 0..7")
for num in (1,5,20):
    e=F(num,1000)
    V=[F(i) for i in range(7)]+[F(7)+e]
    report(V,f"AP with v7 perturbed by {e}")
