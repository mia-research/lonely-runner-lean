"""If a profile's TOTAL blocking pairs < its TOTAL candidates, some candidate has zero blockers
-- a witness, by pigeonhole.  That is a provable sufficient condition.  How much does it settle?"""
import random
from itertools import combinations

def cands(sk):
    A = sk + ((1-sk) % 8); out = []
    while A <= 7*sk: out.append(A); A += 8
    return out

def stats(S):
    """(total candidates, total blocking pairs, min blockers over candidates)"""
    tc = tb = 0; mn = 99
    for sk in S:
        for A in cands(sk):
            tc += 1; c = 0
            for si in S:
                if si == sk or si == 1: continue
                M = 8*sk; r = (si*A) % M
                if min(r, M-r) < sk: c += 1
            tb += c; mn = min(mn, c)
    return tc, tb, mn

# exhaustive Branch B, readings [2,30]
settled = tot = 0; unsettled_with_witness = 0; unsettled_none = []
for combo in combinations(range(2, 31), 6):
    if not any(x % 8 == 0 for x in combo): continue
    S = (1,) + combo; tot += 1
    tc, tb, mn = stats(S)
    if tb < tc:
        settled += 1
        assert mn == 0, S               # pigeonhole must deliver
    else:
        if mn == 0: unsettled_with_witness += 1
        else: unsettled_none.append(S)
print(f"EXHAUSTIVE Branch B, readings [2,30]: {tot:,} profiles\n")
print(f"  settled by pigeonhole alone (blocking pairs < candidates) : {settled:,}"
      f"   ({100*settled/tot:.2f}%)")
print(f"  not settled, but a witness exists anyway                  : {unsettled_with_witness:,}"
      f"   ({100*unsettled_with_witness/tot:.2f}%)")
print(f"  not settled AND no witness                                : {len(unsettled_none):,}")
