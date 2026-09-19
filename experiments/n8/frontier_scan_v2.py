"""v1's 'endpoint' rule was the whole candidate set -- circular.  Rules must NAME a candidate."""
from fractions import Fraction as F
from itertools import combinations
from math import gcd

def clear_x(S, x):
    for s in S:
        y = F(s)*x
        if abs(y - 8*round(y/8)) < 1: return False
    return True

def first_ep(S, s):
    """The FIRST candidate of reading s: smallest (8k+1)/s that is >= 1."""
    k = 0
    while F(8*k+1, s) < 1: k += 1
    x = F(8*k+1, s)
    return clear_x(S, x) if x <= 7 else False

def ep_of(sel):
    return lambda S: first_ep(S, sel(S))

RULES = {
 "first cand of the collider":  ep_of(lambda S: min(s for s in S if s % 8 == 0)),
 "first cand of s_max":         ep_of(lambda S: max(S)),
 "first cand of 2nd largest":   ep_of(lambda S: sorted(S)[-2]),
 "first cand of largest odd":   ep_of(lambda S: max(s for s in S if s % 2)),
 "any of those four":           lambda S: any(f(S) for f in (
      ep_of(lambda T: min(s for s in T if s%8==0)), ep_of(max),
      ep_of(lambda T: sorted(T)[-2]), ep_of(lambda T: max(s for s in T if s%2)))),
}
CATS = {
 "all Branch B":            lambda S: any(s%8==0 for s in S),
 "exactly one collider":    lambda S: sum(1 for s in S if s%8==0)==1,
 "collider is a power of 2":lambda S: any(s%8==0 and (s&(s-1))==0 for s in S),
 "all non-colliders odd":   lambda S: any(s%8==0 for s in S) and all(s%2 or s%8==0 for s in S),
 "collider = s_max":        lambda S: max(S)%8==0,
 "collider = s_max, rest odd": lambda S: max(S)%8==0 and all(s%2 for s in S if s!=max(S)),
 "pairwise coprime >1":     lambda S: any(s%8==0 for s in S) and all(
                                gcd(a,b)==1 for a,b in combinations([s for s in S if s>1],2)),
}
tot={k:0 for k in CATS}; hit={(c,r):0 for c in CATS for r in RULES}
for combo in combinations(range(2,26),6):
    S=(1,)+combo
    for ck,cf in CATS.items():
        if not cf(S): continue
        tot[ck]+=1
        for rk,rf in RULES.items():
            if rf(S): hit[(ck,rk)]+=1
hdr = "".join(f"{r[:13]:>15}" for r in RULES)
print(f"{'sub-category':<28}{'profiles':>9}{hdr}")
for ck in CATS:
    n=tot[ck]
    if not n: continue
    row="".join(f"{100*hit[(ck,rk)]/n:14.2f}%" for rk in RULES)
    star = "  <-- 100%" if any(hit[(ck,rk)]==n for rk in RULES) else ""
    print(f"{ck:<28}{n:>9,}{row}{star}")
