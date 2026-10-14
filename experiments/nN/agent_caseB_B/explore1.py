import itertools, time, sys
from fractions import Fraction as F
from core import *
from collections import Counter
t=time.time()
cnt=Counter(); maxR=F(0); worst=[]
Rhist=Counter()
n=0
for m in (1,2):
    for rest in itertools.combinations(range(m+1,25),6):
        if not (rest[-1] > 9*m): continue
        rd=normalise((m,)+rest); n+=1
        R,st=first_lonely(rd)
        i,g=largest_gap(rd)
        stop=rd[i]
        blk = stop<=7 and R<=F(7)/stop
        cls = 'R1' if R==1 else ('blk' if blk else 'other')
        cnt[cls]+=1
        Rhist[int(R)]+=1
        if R>maxR: maxR=R
        if R>7: worst.append((rd,R))
print(n,cnt,maxR,float(maxR),time.time()-t)
print(sorted(Rhist.items()))
print(len(worst))
for w in worst[:20]: print([str(x) for x in w[0]], w[1])
