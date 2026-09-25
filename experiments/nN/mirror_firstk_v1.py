import json, os
from collections import Counter
H=[tuple(S) for S in json.load(open('experiments/nN/hard_sets_41_60.json'))]
def good(S,Q,k): return all(Q <= 8*(d*k % Q) <= 7*Q for d in S)
c=Counter(); c2=Counter()
for S in H:
    b,a=sorted(S)[-1],sorted(S)[-2]; Q=a+b; m=min(S)
    ks=[k for k in range(1,Q) if good(S,Q,k)]
    k0=-(-Q//(8*m))            # first k at which the smallest disparity reaches 1/8
    c[ks[0]==k0]+=1
    c2[round(8*m*ks[0]/Q,1)]+=1
print('min lonely k == first k clearing the smallest:', dict(c))
print('8*d_min*k_min/Q distribution:', sorted(c2.items())[:20])
