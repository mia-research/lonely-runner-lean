from type_words_v1 import run
from itertools import combinations
from math import gcd
from functools import reduce
import sys
dm=int(sys.argv[1]); Ns=[int(x) for x in sys.argv[2:]]
for N in Ns:
    bad=[]
    for rest in combinations(range(dm+1,N+1),6):
        c=(dm,)+rest
        if reduce(gcd,c)!=1: continue
        w,r,_,ok=run(c,2000)
        if not ok: bad.append(c)
    print("d_min",dm,"N",N,"unfinished at 2000 moves:",len(bad),bad[:5],flush=True)
    if bad: break
