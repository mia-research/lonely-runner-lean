from itertools import combinations
from functools import reduce
from math import gcd
from fractions import Fraction as Q
import sys

def count_float(D):
    iv=[]
    for s in D:
        w=1.0/(8*s)
        for k in range(0,s+1):
            lo=max(k/s-w,0.0); hi=min(k/s+w,1.0)
            if lo<hi: iv.append((lo,hi))
    iv.sort()
    m=[]
    for lo,hi in iv:
        if m and lo<m[-1][1]-1e-15:
            if hi>m[-1][1]: m[-1][1]=hi
        else: m.append([lo,hi])
    n=0; cur=0.0
    for lo,hi in m:
        if cur<=lo+1e-15: n+=1
        cur=max(cur,hi)
    if cur<=1.0+1e-15: n+=1
    return n

def good_exact(S):
    iv=[]
    for s in S:
        for k in range(0,s+1):
            lo,hi=max(Q(8*k-1,8*s),Q(0)),min(Q(8*k+1,8*s),Q(1))
            if lo<hi: iv.append((lo,hi))
    iv.sort(); m=[]
    for lo,hi in iv:
        if m and lo<m[-1][1]: m[-1][1]=max(m[-1][1],hi)
        else: m.append([lo,hi])
    g=[]; cur=Q(0)
    for lo,hi in m:
        if cur<=lo: g.append((cur,lo))
        cur=max(cur,hi)
    if cur<=1: g.append((cur,Q(1)))
    return [(a,b) for a,b in g if a<=b and not(a==b==0) and not(a==b==1)]

N=int(sys.argv[1]); THRESH=8
best=10**9; mins=[]; n=0; cand=0
for D in combinations(range(1,N+1),7):
    if reduce(gcd,D)!=1: continue
    n+=1
    if count_float(D)>THRESH: continue
    cand+=1
    c=len(good_exact(list(D)))
    if c<best: best=c; mins=[D]
    elif c==best and len(mins)<6: mins.append(D)
print(f'N={N}: {n:,} primitive sets, {cand:,} passed float screen (<= {THRESH})')
print(f'   EXACT minimum count = {best}')
print(f'   minimisers: {mins}')
