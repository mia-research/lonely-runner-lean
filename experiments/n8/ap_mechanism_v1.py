"""DERIVING the 22/7, not fitting it.

At a protected point R (odd), the reading blocking JUST BELOW satisfies s.R = 1 mod 8, so
s = R^-1 = R mod 8 by the Klein group.  R = 7 and R = 15 both give s = 7 mod 8 -- in the AP that is
s_7 = S itself.  So S guards the RIGHT ENDPOINT OF BOTH REGIONS.

Raising S to 7+eps:
  at R = 7:   (7+eps)(7-d) mod 8 = 1 + 7eps - (7+eps)d  >= 1  iff  d <= 7eps/(7+eps) ~ eps
              -> uncovered interval [7-eps, 7], length ~ eps
  at R = 15:  (7+eps)(15-d) mod 8 = 1 + 15eps - (7+eps)d >= 1  iff  d <= 15eps/(7+eps) ~ 15eps/7
              -> uncovered interval [15 - 15eps/7, 15], length ~ 15eps/7
  joint ~ eps + 15eps/7 = (22/7) eps.

Verify: locate the uncovered SET exactly, and check it is those two intervals."""
import sys; sys.path.insert(0,'experiments/n8')
def unc_set(S, lo, hi):
    bad=[]
    for s in S:
        k=0
        while (8*k-1)/s <= hi+1:
            a,b=(8*k-1)/s,(8*k+1)/s
            if b>lo and a<hi: bad.append((max(a,lo),min(b,hi)))
            k+=1
    bad.sort(); merged=[]
    for a,b in bad:
        if merged and a<=merged[-1][1]: merged[-1]=(merged[-1][0],max(merged[-1][1],b))
        else: merged.append((a,b))
    gaps=[]; pos=lo
    for a,b in merged:
        if a>pos: gaps.append((pos,a))
        pos=max(pos,b)
    if pos<hi: gaps.append((pos,hi))
    return gaps
print("  which reading guards each protected point?  (blocks just below R)\n")
print(f"    {'R':>4} {'R mod 8':>8} {'R^-1 mod 8':>11}  guard reading")
for R in (1,3,5,7,9,11,13,15):
    inv=[s for s in range(1,8) if (s*R)%8==1]
    print(f"    {R:>4} {R%8:>8} {inv[0] if inv else '-':>11}  {'s_7 = S' if inv and inv[0]==7 else ('s_1 = 1 (outside the six)' if inv and inv[0]==1 else f's = {inv[0]}')}")
print()
for eps in (0.01, 0.001, 0.0001):
    S=[2.0,3.0,4.0,5.0,6.0,7.0+eps]
    g1=unc_set(S,1.0,7.0); g2=unc_set(S,9.0,15.0)
    L1=sum(b-a for a,b in g1); L2=sum(b-a for a,b in g2)
    print(f"  eps = {eps:g}")
    print(f"    uncovered in [1, 7]: {[(round(a,8),round(b,8)) for a,b in g1]}  total {L1:.10f}   predicted {7*eps/(7+eps):.10f}")
    print(f"    uncovered in [9,15]: {[(round(a,8),round(b,8)) for a,b in g2]}  total {L2:.10f}   predicted {15*eps/(7+eps):.10f}")
    print(f"    joint {L1+L2:.10f}   predicted (22/7)eps = {22*eps/7:.10f}   exact 22eps/(7+eps) = {22*eps/(7+eps):.10f}")
    print()
