from math import gcd
from fractions import Fraction as F
def clear_int(e, r, N):
    R = (e*r) % N; return N <= 8*R <= 7*N
def blocked_direct(e, s): return {r for r in range(1, 8*s, 2) if not clear_int(e, r, 8*s)}
def blocked_formula(e, s):
    h = gcd(e, 8*s); m = 8*s//h; u = e//h
    if m == 1: return set(range(1, 8*s, 2)), "dead: on the subject at every AP time"
    near = lambda x: 8*x < m or 8*x > 7*m            # residue within m/8 of 0
    B = {r for r in range(1, 8*s, 2) if near((u*r) % m)}
    if m % 2 == 0 and m <= 8: kind = "never in the way"
    elif m % 2 == 0: kind = f"in the way at {len(B)} of {4*s} times (m={m} even)"
    else: kind = f"in the way at {len(B)} of {4*s} times (m={m} odd, includes r = 0 mod {m})"
    return B, kind
# check the derivation against direct computation
bad = sum(blocked_direct(e, s) != blocked_formula(e, s)[0] for e in range(1, 400) for s in range(1, 41))
print(f"derivation vs direct, e in [1,399], s in [1,40]: {399*40} cases, disagreements {bad}")
assert bad == 0

V = (1,31,75,97,128,160,176,225)
def explain(i, scales):
    ds = [abs(v-V[i]) for j, v in enumerate(V) if j != i]
    print(f"\nrunner at speed {V[i]}, differences {ds}")
    for s in scales:
        taken = set(); lines = []
        for e in ds:
            B, kind = blocked_formula(e, s); taken |= B
            lines.append(f"      {e:>4} = 8s*{F(e, 8*s)}  {kind}")
        free = sorted(set(range(1, 8*s, 2)) - taken)
        print(f"   scale {s}: AP times t = r/{8*s}, odd r below {8*s}; free r = {free if free else 'NONE'}")
        for l in lines: print(l)
explain(0, [1, 2, 3, 4, 5])
explain(3, [5, 7])
