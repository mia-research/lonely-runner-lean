"""Branch B without the bound.  First: WHERE is the gap in the minimiser [3,4,5,7,11,24]?

Structure to exploit: a reading s = 8b has bad set ((m - 1/8)/b, (m + 1/8)/b) -- a comb of period
1/b centred on the multiples of 1/b.  For b = 1 (s = 8) that is a neighbourhood of every integer,
width 1/4.  So a multiple of 8 blocks all the integers -- including the eight odd ones that Branch A
relies on.  The question is where it then FAILS to cover."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
def gaps(S, lo, hi):
    bad=[]
    for s in S:
        k=0
        while F(8*k-1,1)/s <= hi+1:
            a,b=F(8*k-1,1)/s, F(8*k+1,1)/s
            if b>lo and a<hi: bad.append((max(a,F(lo)),min(b,F(hi))))
            k+=1
    bad.sort(); merged=[]
    for a,b in bad:
        if merged and a<=merged[-1][1]: merged[-1]=(merged[-1][0],max(merged[-1][1],b))
        else: merged.append((a,b))
    out=[]; pos=F(lo)
    for a,b in merged:
        if a>pos: out.append((pos,a))
        pos=max(pos,b)
    if pos<F(hi): out.append((pos,F(hi)))
    return out
for name,prof in (("minimiser",[3,4,5,7,11,24]),
                  ("with s=8",[2,3,4,5,7,8]),
                  ("AP + 8",[3,4,5,6,7,8]),
                  ("AP with 6->8",[2,3,4,5,7,8])):
    S=[F(x) for x in prof]
    g1=gaps(S,1,7); g2=gaps(S,9,15)
    L=sum(b-a for a,b in g1)+sum(b-a for a,b in g2)
    print(f"  {name:>14} {prof}")
    print(f"      gaps in [1,7] : {[(str(a),str(b)) for a,b in g1]}")
    print(f"      gaps in [9,15]: {[(str(a),str(b)) for a,b in g2]}")
    print(f"      total uncovered {L} = {float(L):.8f}")
    # which reading is missing / who would have guarded
    print(f"      readings mod 8: {[x%8 for x in prof]}")
    print()
