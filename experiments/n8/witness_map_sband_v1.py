# PREREG: docs/n8/PREREG_WITNESS_PERTURBATION_v1.md
# Primary statistic S(ds) = supporting flank set, exhaustive past the contaminated H<=30 window.
# Exact integer arithmetic only (no floats). Residues stepped incrementally: r_{k+1} = r_k + 8d mod 8e.
from itertools import combinations
from math import gcd
import sys, collections

def supporting(ds):
    """set of flanks e in ds that host at least one witness k in [0,e)"""
    out=[]
    for e in ds:
        M=8*e; lo=e; hi=7*e
        r=[d % M for d in ds]          # k=0 residues
        step=[(8*d) % M for d in ds]
        found=False
        for k in range(e):
            ok=True
            for i in range(7):
                if not (lo <= r[i] <= hi): ok=False; break
            if ok: found=True; break
            for i in range(7): r[i]=(r[i]+step[i]) % M
        if found: out.append(e)
    return out

H=int(sys.argv[1]) if len(sys.argv)>1 else 40
hist=collections.Counter(); minimal=[]; zero=[]; n=0
for c in combinations(range(1,H+1),7):
    g=0
    for x in c: g=gcd(g,x)
    if g!=1: continue
    n+=1
    s=supporting(c); m=len(s)
    hist[m]+=1
    if m==0: zero.append(c)
    elif m==1: minimal.append((c,s[0]))
print(f"exhaustive primitive 7-subsets of [1,{H}]: {n}")
print(f"|S| distribution: {dict(sorted(hist.items()))}")
print(f"|S| = 0  (would refute LRC at 8): {len(zero)}   {zero[:5]}")
print(f"|S| = 1: {len(minimal)}")
for c,e in minimal:
    print(f"   {c}  ->  sole flank {e}   (is max: {e==max(c)})")
