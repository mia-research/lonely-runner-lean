"""'At least two readings supply a witness' -- 244,790 profiles, never 1, never 0.  WHY?

The walk (edge_witness_both) gives a RIGHT-endpoint witness for some reading s and a LEFT-endpoint
witness for some s'.  If s != s' that is two suppliers.  Measure whether the walk's two readings
actually differ, and look at the tight cases (exactly 2 suppliers).
"""
from fractions import Fraction as F
from itertools import combinations

def clear_x(S, x):
    for s in S:
        y = F(s)*x
        if abs(y - 8*round(y/8)) < 1: return False
    return True

def supplies_right(S, s):
    """Some (8k+1)/s in [1,7] is clear."""
    k = 0
    while F(8*k+1, s) <= 7:
        if F(8*k+1, s) >= 1 and clear_x(S, F(8*k+1, s)): return True
        k += 1
    return False

def walk_endpoints(S):
    """Take a witness, walk down to a right endpoint and up to a left endpoint. Return (s_down,s_up)."""
    # find any witness on the exact candidate grid
    cands = []
    for s in S:
        k = 0
        while F(8*k+1, s) <= 7:
            x = F(8*k+1, s)
            if x >= 1: cands.append(x)
            k += 1
    cands = sorted(set(cands))
    w = next((x for x in cands if clear_x(S, x)), None)
    if w is None: return None
    # the reading whose right endpoint w is
    down = [s for s in S if (w*s).denominator == 1 and (int(w*s) - 1) % 8 == 0]
    up   = [s for s in S if (w*s).denominator == 1 and (int(w*s) + 1) % 8 == 0]
    return down, up

tot = 0; cnt = {}; tight = []
for combo in combinations(range(2, 24), 6):
    if not any(x % 8 == 0 for x in combo): continue
    S = (1,) + combo
    sup = [s for s in S if supplies_right(S, s)]
    tot += 1
    cnt[len(sup)] = cnt.get(len(sup), 0) + 1
    if len(sup) == 2 and len(tight) < 6: tight.append((S, sup))
print(f"Branch B, readings [2,23] : {tot:,}")
print(f"  number of readings supplying a RIGHT-endpoint witness: {dict(sorted(cnt.items()))}")
print(f"  minimum = {min(cnt)}\n")
print("  the tight cases (exactly 2 suppliers):")
for S, sup in tight:
    print(f"    S={S}  suppliers={sup}   colliders={[s for s in S if s%8==0]}")
