# characterise block failures (largest-gap split) on integer sets
import itertools
from fractions import Fraction as F
from core import *
from collections import Counter
c=Counter(); ex=[]
for m in (1,2):
    for rest in itertools.combinations(range(m+1,25),6):
        if not (rest[-1] > 9*m): continue
        rd=normalise((m,)+rest)
        R,st=first_lonely(rd)
        i,g=largest_gap(rd); stop=rd[i]
        if stop>7: c['stop>7']+=1; continue
        if R<=7/stop: continue
        j=6-i
        # reason: some fast reading blocked on whole block?
        beta=F(7)/stop
        whole=[f for f in rd[i+1:] if next_clear_start(f,F(1))>beta]
        c[(j,'single_whole' if whole else 'joint')]+=1
        if len(ex)<30: ex.append(((m,)+rest,str(R),str(stop),j,[str(x) for x in whole]))
print(c)
for e in ex: print(e)
