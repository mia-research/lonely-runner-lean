"""BSM discipline: the AP is a boundary configuration, so the zero is only attained EXACTLY.
Float hill-climbing cannot sit on it -- that is machine-limit fragility, not evidence of anything.
Redo the functional in exact rationals and get the local behaviour in ALL SIX directions.

If every direction has a strictly positive first-order rate, the AP is a strict local minimum of the
uncovered-length functional, and only global structure remains."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
def unc_exact(S, lo, hi):
    """exact uncovered length of [lo,hi] under the open bad sets of readings S"""
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
    u=F(hi)-F(lo)
    for a,b in merged: u-=(b-a)
    return u
def joint(S): return unc_exact(S,1,7)+unc_exact(S,9,15)
AP=[F(2),F(3),F(4),F(5),F(6),F(7)]
print(f"  AP, exact: joint uncovered = {joint(AP)}\n")
print("  first-order rate in each coordinate direction (exact rationals)\n")
print(f"  {'coord':>6} {'dir':>4} " + "".join(f"{f'eps=1/{d}':>14}" for d in (100,1000,10000)) + "   rate")
for i in range(6):
    for sgn in (+1,-1):
        vals=[]
        for den in (100,1000,10000):
            e=F(sgn,den)
            S=list(AP); S[i]=S[i]+e
            if S[i]<=1 or any(S[j]>=S[j+1] for j in range(5)): vals.append(None); continue
            vals.append(joint(sorted(S)))
        cells="".join(f"{(float(v) if v is not None else float('nan')):>14.8f}" for v in vals)
        rate = (float(vals[2])*10000) if vals[2] is not None else float('nan')
        print(f"  {float(AP[i]):>6} {('+' if sgn>0 else '-'):>4} {cells}   {rate:.5f}")
print()
print("  reading the rates: rate = uncovered / eps as eps -> 0")
print("  a strictly positive rate in every direction = the AP is a strict local minimum")
