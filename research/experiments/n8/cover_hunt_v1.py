from fractions import Fraction as F
from math import gcd
import random
def frac(x):
    r=x-int(x); return r+1 if r<0 else r
def nrm(x):
    f=frac(x); return min(f,1-f)
random.seed(3)
for Q in (13,19,25,31,40):
    C=sorted({F(p,q) for q in range(2,Q+1) for p in range(1,q)
              if gcd(p,q)==1 and F(1,8)<=F(p,q)<=F(7,8)})
    n=len(C)
    pool=sorted({F(a,b) for b in (1,2,3,5,7,11,13,17,19,23) for a in range(b,2600)})
    M={}
    for s in pool:
        m=0
        for k,u in enumerate(C):
            if nrm(s*u)<F(1,8): m|=1<<k
        if m: M.setdefault(m,s)
    masks=sorted(M, key=lambda m:-bin(m).count('1'))[:1500]
    best=0; bestset=None
    for _ in range(20000):
        cur=0; ch=[]
        for _ in range(6):
            cand=[x for x in random.sample(masks,min(60,len(masks))) if M[x] not in ch]
            if not cand: break
            mm=max(cand,key=lambda m:bin(m&~cur).count('1'))
            cur|=mm; ch.append(M[mm])
        c=bin(cur).count('1')
        if c>best: best,bestset=c,list(ch)
    print('Q=%-3d |C|=%-4d  best cover by 6 DISTINCT readings: %3d/%-4d uncovered %-4d %s'
          % (Q,n,best,n,n-best,'COVER FOUND' if best==n else 'no cover found'))
    if best==n: print('        readings %s' % [str(x) for x in bestset])
