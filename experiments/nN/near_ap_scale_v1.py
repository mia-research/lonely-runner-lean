"""Deformations of the AP at large scale -- the sets a scale-blind test never draws.

AP (1..7) is scale invariant: k*(1..7) has common factor k and reduces to the AP.  Its primitive
deformations S = {k*i + e_i}, e_i in [-3, 3], k = 10^2, 10^3, 10^4, have their lonely instants near
1/(8k) (the AP spine at scale k).  For each: is it in EightResidual (all v5 fields + no clearing
resolution D <= 64)?  The least clearing resolution D* (ladder, cap 5k)?  And a certificate at its own
flanks (least opening (j + 1/8)/e, e in S, exact integer band test)?
"""
exec(open('residual_members_v1.py').read().split("L = 8 * lcm")[0])
from collections import Counter
rnd = random.Random(35)
def least_D(S, cap):
    for D in range(1, cap + 1):
        if any(clears(S, D, 8 * j + 1) for j in range(D)): return D
    return None
def band(S, e, j): return all(e <= d * (8 * j + 1) % (8 * e) <= 7 * e for d in S)
for k in (100, 1000, 10000):
    mem = 0; tot = 0; Dstar = Counter(); ex = None
    while tot < 200:
        S = tuple(sorted(k * i + rnd.randrange(-3, 4) for i in range(1, 8)))
        if len(set(S)) < 7 or reduce(gcd, S) > 1: continue
        tot += 1
        if not residual(S): continue
        mem += 1
        D = least_D(S, 5 * k); Dstar['<=64' if D and D <= 64 else ('<=k' if D and D <= k else ('<=5k' if D else '>5k'))] += 1
        if ex is None: ex = (S, D)
    print(f"k={k}: primitive deformations {tot}; in EightResidual {mem};  least clearing resolution: {dict(Dstar)};  example {ex}")
