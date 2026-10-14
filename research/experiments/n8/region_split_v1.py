"""KEY SPLIT: the region is [1,7] u [9,15], and s_1 = 1's own bad interval is exactly (7,9).  So no
chain crosses the gap -- the two regions must be covered INDEPENDENTLY by the same six combs.

In [9,15] the multipliers are far smaller.  At reach x, using comb s at level m needs
(8m-1)/s < x < (8m+1)/s, so 8m ~ s.x, and the multiplier (8m+1)/(8m-1) ~ 1 + 2/(s.x).  At x = 9 the
smallest usable m is 2 (since (8m+1)u > 9 with u < 1 forces 8m+1 > 9), giving at most 17/15 = 1.133
against 9/7 = 1.286 at x = 1.

Compute the exact per-step ceiling across both regions, and what each region costs in steps."""
from math import log, ceil
NC=6
def max_mult_at(x, smin=1.0, smax=8.0):
    """largest (8m+1)/(8m-1) available at reach x over admissible s and integer m"""
    best=1.0; arg=None
    for m in range(1,200):
        # need (8m-1)/s < x < (8m+1)/s  =>  s in ((8m-1)/x, (8m+1)/x)
        lo=(8*m-1)/x; hi=(8*m+1)/x
        lo2=max(lo,smin); hi2=min(hi,smax)
        if lo2<hi2:
            mult=(8*m+1)/(8*m-1)
            if mult>best: best, arg = mult,(m,(lo2,hi2))
    return best, arg
print("  per-step ceiling on the reach multiplier, by position\n")
print(f"  {'x':>7} {'max mult':>10} {'at m':>6}  admissible s")
for x in (1.0, 1.5, 2.0, 3.0, 5.0, 7.0, 9.0, 11.0, 13.0, 15.0):
    mm,arg=max_mult_at(x)
    m,(lo,hi)=arg
    print(f"  {x:>7.2f} {mm:>10.5f} {m:>6}  ({lo:.4f}, {hi:.4f})")
print()
def steps_needed(a,b):
    """greedy lower bound: walk from a to b always taking the best available multiplier,
       with at most NC steps at each level m (one interval per comb per level)"""
    x=a; n=0; used={}
    while x<b and n<400:
        best=1.0; bm=None
        for m in range(1,300):
            lo=(8*m-1)/x; hi=(8*m+1)/x
            if hi<=1.0 or lo>=8.0: continue
            if used.get(m,0)>=NC: continue
            mult=(8*m+1)/(8*m-1)
            if mult>best: best,bm=mult,m
        if bm is None: return None
        used[bm]=used.get(bm,0)+1
        x*=best; n+=1
    return n
a=steps_needed(1.0,7.0); b=steps_needed(9.0,15.0)
print(f"  lower bound on intervals needed:")
print(f"    cover [1, 7]  : {a} intervals")
print(f"    cover [9,15]  : {b} intervals")
print(f"    BOTH          : {a+b} intervals, from six combs")
print()
print("  how many intervals do six combs even HAVE in each region?")
for lab,(lo,hi) in (("[1,7]",(1.0,7.0)),("[9,15]",(9.0,15.0))):
    print(f"    {lab}: comb with reading s has intervals at m with (8m+1)/s in [{lo},{hi}]:")
    for s in (1.2, 2.5, 4.0, 5.5, 7.45):
        ms=[m for m in range(0,200) if lo <= (8*m+1)/s <= hi]
        print(f"        s = {s:>5}: {len(ms)} intervals (m = {ms[:6]}{'...' if len(ms)>6 else ''})")
