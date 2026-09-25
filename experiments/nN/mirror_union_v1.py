import json
from statistics import mean
H=[tuple(S) for S in json.load(open('experiments/nN/hard_sets_41_60.json'))]
def blocked(d,Q): return {k for k in range(1,Q) if not (Q <= 8*(d*k % Q) <= 7*Q)}
ub=[]; act=[]; mx=[]
for S in H:
    b,a=sorted(S)[-1],sorted(S)[-2]; Q=a+b
    B=[blocked(d,Q) for d in S if d!=b]          # b reads as -a: merged with a
    ub.append(sum(len(x) for x in B)/(Q-1)); act.append(len(set().union(*B))/(Q-1)); mx.append(max(len(x) for x in B)/(Q-1))
print(f"mirror modulus, 6 effective constraints: union-bound total {mean(ub):.2f} (min {min(ub):.2f}); actual blocked {mean(act):.2f} (max {max(act):.2f}); largest single {mean(mx):.2f}")
