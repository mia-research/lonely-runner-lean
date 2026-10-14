# Exact: which sets of n-1 distinct positive integer disparities (<= N) are settled by gcd-descent, R1, R6, R5 alone; uncovered sets are run through the cascade (exact Fractions).
import sys, itertools, math
from fractions import Fraction as F
def settled(S,n):
    g=0
    for d in S: g=math.gcd(g,d)
    if g>1: return settled(tuple(d//g for d in S),n)
    if max(S)<=(n-1)*min(S): return 'R1'
    for q in range(2,n+1):
        if all(d%q for d in S): return 'R6'
    M=[d for d in S if d%n==0]
    if len(M)>=len(S)-1 and M:
        return settled(tuple(d//n for d in M),n) and 'R5'
    return None
def cascade_lonely(S,n,cap=10**6):
    t=F(1,n*min(S)); 
    def dist(x): x-=math.floor(x); return min(x,1-x)
    for _ in range(cap):
        w=[d for d in S if dist(d*t)<F(1,n)]
        if not w: return t
        t=max(F(math.floor(d*t-F(1,n))+1)/d+F(1,n)/d for d in w)
    return None
n=int(sys.argv[1]); N=int(sys.argv[2])
tot=0; unc=[]; byrule={}
for S in itertools.combinations(range(1,N+1),n-1):
    tot+=1
    r=settled(S,n)
    if r: byrule[r]=byrule.get(r,0)+1
    else: unc.append(S)
bad=[S for S in unc if cascade_lonely(S,n) is None]
print(f"n={n} N={N} sets={tot} by_rule={byrule} uncovered={len(unc)} cascade_failed={len(bad)} example_uncovered={unc[:3]}")
