import sys
from type_words_v1 import run
from itertools import combinations
from math import gcd
from functools import reduce
for dm in (1,2,3,5):
    out=[]
    for N in (12,16,20,24,28):
        if dm==1 and N>24: continue
        if dm>1 and N>20: continue
        S=set();cnt=0
        for rest in combinations(range(dm+1,N+1),6):
            c=(dm,)+rest
            if reduce(gcd,c)!=1: continue
            cnt+=1
            w,r,_,ok=run(c)
            assert ok
            S.add(tuple(s for s,_ in w))
        out.append((N,cnt,len(S)))
    print("d_min",dm,out,flush=True)
