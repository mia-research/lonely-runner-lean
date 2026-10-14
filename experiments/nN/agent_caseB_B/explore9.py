import random, math, sys
from fractions import Fraction as F
from core import *
from conditions import *
from collections import Counter
random.seed(11)
D=2520
def sample(mode):
    top=random.randint(9*D+1,24*D)
    if mode=='u': xs=random.sample(range(D+1,top),5)
    else:
        xs=set()
        while len(xs)<5:
            v=int(round(D*math.exp(random.uniform(0,math.log(top/D)))))
            if D<v<top: xs.add(v)
        xs=list(xs)
    return [F(1)]+sorted(F(x,D) for x in xs)+[F(top,D)]
tot=Counter(); cov=Counter(); covX=Counter()
for mode in ('u','log'):
  for _ in range(3000):
    rd=sample(mode)
    i,g=largest_gap(rd); j=6-i
    key=(j, 'stop<=7' if rd[i]<=7 else 'stop>7')
    tot[key]+=1
    d=any(fn(rd) is not None for n,fn in DERIVED)
    cov[key]+=d
    if not d: covX[key]+= X0_stair5(rd) is not None
for k in sorted(tot): print(k,tot[k],cov[k],covX[k])
