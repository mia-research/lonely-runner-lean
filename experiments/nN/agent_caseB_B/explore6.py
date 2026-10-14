import random, math, sys
from fractions import Fraction as F
from core import *
from conditions import *
from collections import Counter
random.seed(7)
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
N=int(sys.argv[1])
for mode in ('u','log'):
    c=Counter(); cum=Counter()
    for _ in range(N):
        rd=sample(mode)
        fired=set()
        for name,fn in DERIVED+EXACT:
            R=fn(rd)
            if R is not None:
                assert lonely_at(rd,R) and R<=15,(name,rd,R)
                fired.add(name); c[name]+=1
        d=[n for n,_ in DERIVED]
        if fired & {'C0_R1','C1_escape'}: cum['a:C0C1']+=1
        if fired & {'C0_R1','C1_escape','C2_lacunary'}: cum['b:+C2']+=1
        if fired & set(d): cum['c:allD']+=1
        if fired & (set(d)|{'X1_block_largest_gap'}): cum['d:+X1']+=1
        if fired & (set(d)|{'X1_block_largest_gap','X2_greedy3'}): cum['e:+X2']+=1
        if fired: cum['f:all']+=1
    print(mode,N,sorted(c.items()),sorted(cum.items()))
