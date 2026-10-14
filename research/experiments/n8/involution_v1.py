"""Solutions come in a minimum of 2, never 1.  Is there an involution?

Candidate: the bad interval of reading s has TWO endpoints, (8k-1)/s and (8k+1)/s.  reach_mem
returns right endpoints; time reversal tau -> 1-tau should swap the families.  In q terms
tau = (8q+1)/(8m) maps to (8(m-q-1)+7)/(8m).  Test q -> m-1-q and other candidates.
"""
from itertools import combinations
def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def sols(m, bs):
    cond = [(b,)+I(b) for b in bs] + [(m,)+I(m)]
    return sorted(q for q in range(m) if all(lo <= q % b <= hi for b,lo,hi in cond))

tight = []
for m in range(24, 320):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    mid = [d for d in ds if d != 1 and d != m]
    for c in combinations(mid, 5):
        bs = sorted(m//s for s in c)
        S = sols(m, bs)
        if len(S) <= 3: tight.append((m, bs, S))
print(f"profiles with <= 3 solutions: {len(tight)}\n")
for m, bs, S in tight[:10]:
    print(f"  m={m:<4} b={bs}  solutions={S}")
    print(f"        m-1-q -> {[m-1-q for q in S]}   {'CLOSED' if sorted(m-1-q for q in S)==S else ''}")
print()
# test candidate involutions globally
import random
cands = {"m-1-q": lambda q,m: (m-1-q) % m, "m-q": lambda q,m: (m-q) % m,
         "-q-1": lambda q,m: (-q-1) % m, "m//2+q": lambda q,m: (m//2+q) % m}
res = {k: [0,0] for k in cands}
for m, bs, S in tight:
    Ss = set(S)
    for k, f in cands.items():
        res[k][1] += 1
        if {f(q,m) for q in S} == Ss: res[k][0] += 1
for k,(a,b) in res.items():
    print(f"  involution '{k}':  preserves the solution set in {a}/{b} tight profiles")
