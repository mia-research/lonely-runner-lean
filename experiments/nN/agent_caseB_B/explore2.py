import random, time
from fractions import Fraction as F
from core import *
from collections import Counter
random.seed(1)
D=2520
def sample(mode):
    while True:
        top=random.randint(9*D+1,24*D)
        if mode=='u':
            xs=random.sample(range(D+1,top),5)
        else:
            import math
            xs=set()
            while len(xs)<5:
                v=int(round(D*math.exp(random.uniform(0,math.log(top/D)))))
                if D<v<top: xs.add(v)
            xs=list(xs)
        return [F(1)]+sorted(F(x,D) for x in xs)+[F(top,D)]
for mode in ('u','log'):
    st=Counter(); Rh=Counter(); mx=F(0); cls=Counter()
    for _ in range(20000):
        rd=sample(mode)
        R,s=first_lonely(rd)
        st[s]+=1; Rh[int(R)]+=1; mx=max(mx,R)
        i,g=largest_gap(rd); stop=rd[i]
        cls['R1' if R==1 else ('blk' if stop<=7 and R<=7/stop else 'other')]+=1
    print(mode,sorted(st.items()),sorted(Rh.items()),float(mx),cls)
