"""The tension, pushed to a decision.

FACT A (computed): the gap (9/S, 15/S) inside [1,7] can only be met by readings s in [3.48, 7.99].
FACT B: an m=2 interval (15/s, 17/s) meets [9,15] only if s < 17/9 = 1.889.
So a comb cannot do both.

THE QUESTION: can [9,15] be covered WITHOUT any comb below 1.889?  If not, the two demands are
incompatible and band 2 is unreachable.

Compute the maximum reach from 9 using only combs with s >= 1.889, honouring one interval per comb
per level."""
import numpy as np
def max_reach(start, target, smin, smax, ncombs=6, profile=None):
    """greedy: from `start`, always take the largest available multiplier.
       If `profile` is given, use exactly those combs; else allow any s in [smin,smax]
       (an UPPER bound on what any profile could do)."""
    x=start; n=0; used={}
    while x<target and n<500:
        best=1.0; bm=None; bs=None
        for m in range(1,400):
            lo=(8*m-1)/x; hi=(8*m+1)/x
            if profile is None:
                a,b=max(lo,smin),min(hi,smax)
                if a>=b: continue
                if used.get(m,0)>=ncombs: continue
                mult=(8*m+1)/(8*m-1)
                if mult>best: best,bm,bs=mult,m,a
            else:
                for s in profile:
                    if lo<s<hi and used.get((m,s),0)==0:
                        mult=(8*m+1)/(8*m-1)
                        if mult>best: best,bm,bs=mult,m,s
        if bm is None: return x,n,False
        if profile is None: used[bm]=used.get(bm,0)+1
        else: used[(bm,bs)]=1
        x*=best; n+=1
    return x,n,(x>=target)
print("  MAXIMUM POSSIBLE reach in [9,15], as a function of the smallest allowed reading\n")
print(f"  {'s_min allowed':>14} {'max reach from 9':>18} {'steps':>7} {'covers [9,15]?':>16}")
for smin in (1.01, 1.2, 1.5, 1.889, 2.0, 2.5, 3.0, 3.48, 4.0, 5.0):
    x,n,ok = max_reach(9.0, 15.0, smin, 8.0)
    print(f"  {smin:>14.3f} {x:>18.5f} {n:>7} {str(ok):>16}")
print()
print("  -> this is an UPPER bound over ALL profiles with readings in [s_min, 8].")
print()
print("  Now the same for [1,7], as a function of the LARGEST allowed reading below S:")
print(f"  {'s_max allowed':>14} {'max reach from 1':>18} {'steps':>7} {'covers [1,7]?':>16}")
for smax in (1.889, 2.5, 3.48, 4.0, 5.0, 6.0, 7.0, 7.99):
    x,n,ok = max_reach(1.0, 7.0, 1.01, smax)
    print(f"  {smax:>14.3f} {x:>18.5f} {n:>7} {str(ok):>16}")
