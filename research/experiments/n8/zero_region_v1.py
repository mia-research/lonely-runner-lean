"""The zero set is a REGION: the units 3,5,7 appear pinned, the non-units 2,4,6 float.
Find the exact region, and check what is invariant across it.

If the units are pinned at 3,5,7 throughout, then the eight protected points stay guarded, the clear
set stays non-empty, and the reduction becomes

    uncovered = 0  =>  units are 3,5,7  =>  eight protected points clear  =>  R < 16

which is weaker than uniqueness of the AP and therefore easier."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
def unc_exact(S, lo, hi):
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
def clear_pts(S):
    return [R for R in (1,3,5,7,9,11,13,15) if all(1 <= (s*R)%8 <= 7 for s in [F(1)]+list(S))]
def bisect(lo, hi, build, want_zero_at_lo=True, iters=40):
    L,H=F(lo),F(hi)
    for _ in range(iters):
        M=(L+H)/2
        if (joint(build(M))==0)==want_zero_at_lo: L=M
        else: H=M
    return L,H
print("  exact zero region in each NON-UNIT coordinate (others held at the AP)\n")
for i,base in ((0,F(2)),(2,F(4)),(4,F(6))):
    def build(x, i=i):
        S=[F(2),F(3),F(4),F(5),F(6),F(7)]; S[i]=x; return sorted(S)
    up=bisect(base, base+1, build)
    dn=bisect(base, base-1, build)
    print(f"    reading {base}: zero for s in ({float(dn[1]):.8f}, {float(up[0]):.8f})")
    print(f"       upper edge between {up[0].limit_denominator(2000)} and {up[1].limit_denominator(2000)}")
    print(f"       lower edge between {dn[1].limit_denominator(2000)} and {dn[0].limit_denominator(2000)}")
print()
print("  and the UNITS -- is the zero attained anywhere but exactly 3, 5, 7?")
for i,base in ((1,F(3)),(3,F(5)),(5,F(7))):
    def build(x, i=i):
        S=[F(2),F(3),F(4),F(5),F(6),F(7)]; S[i]=x; return sorted(S)
    hits=[]
    for num in range(-20,21):
        if num==0: continue
        x=base+F(num,1000)
        if joint(build(x))==0: hits.append(x)
    print(f"    reading {base}: zero at {len(hits)} of 40 nearby rationals (step 1/1000)  {hits[:4]}")
print()
print("  clear points across the zero region (non-units moved, units fixed):")
for s2,s4,s6 in ((F(2),F(4),F(6)),(F(201,100),F(4),F(6)),(F(2),F(401,100),F(6)),
                 (F(2),F(4),F(601,100)),(F(201,100),F(401,100),F(601,100))):
    S=sorted([s2,F(3),s4,F(5),s6,F(7)])
    print(f"    {[str(x) for x in S]}  uncovered {joint(S)}  clear {clear_pts(S)}")
