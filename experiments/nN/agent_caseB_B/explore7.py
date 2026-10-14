import random, math, sys
from fractions import Fraction as F
from core import *
from conditions import *
from collections import Counter
random.seed(8)
D=2520
def sample():
    top=random.randint(9*D+1,24*D)
    xs=random.sample(range(D+1,top),5)
    return [F(1)]+sorted(F(x,D) for x in xs)+[F(top,D)]
c=Counter(); shown=0
for _ in range(3000):
    rd=sample()
    if any(fn(rd) is not None for n,fn in DERIVED): continue
    R,st=first_lonely(rd)
    laps=[lap_of(s,R) for s in rd]
    # group structure of laps
    c[tuple(laps)]+=1
    if shown<25:
        shown+=1
        i,g=largest_gap(rd)
        print([round(float(x),3) for x in rd], 'R=',round(float(R),4),'laps',laps,'gap@',i,round(float(g),3))
print(len(c), c.most_common(15))
