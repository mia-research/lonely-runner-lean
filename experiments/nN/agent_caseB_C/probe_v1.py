from fractions import Fraction as F
import random
from core import least_m, lonely_at
S=tuple(F(v) for v in ['1','2.3509','3.2412','4.1886','5.2223','5.7871','7.4378'])
print(least_m(S,M=40))
# minimal lonely R by scan over breakpoints (exact): candidate R = (8k+1)/s_i
def min_lonely(S, Rmax=200):
    c=[]
    for s in S:
        k=0
        while (8*k+1)/s<=Rmax:
            c.append(F(8*k+1)/s); k+=1
    for R in sorted(c):
        if lonely_at(S,R): return R
print('min lonely R', float(min_lonely(S)))
random.seed(1)
from collections import Counter
cnt=Counter()
for t in range(300):
    top=random.randint(7*2520+1,24*2520)
    mids=sorted(random.sample(range(2521,top),5))
    S=tuple(F(v,2520) for v in [2520]+mids+[top])
    r=least_m(S,M=12)
    cnt[None if r is None else r[0]]+=1
print(cnt)
