"""Residual members with NO separation of scale (max/min < 9), so no block split, fast pair or R8.

One runner d1 = 8*lcm(1..64)*u kills every lattice D <= 64.  A single multiple of 8 with odd others
is always caught by the free flank (each odd runner blocks at most one of the seven shifts), so the
other six are drawn with MIXED residues mod 8: 1 to 3 further multiples of 8, the rest random, all
in (d1/8.9, d1] with spread forced above 7.  Test every residual field computable at this size, then
run the ladder past 64 (least D <= 20000 with a clearing numerator 8j+1, integer band test).
"""
exec(open('residual_members_v1.py').read().split("L = 8 * lcm")[0])
from math import lcm
from collections import Counter
L = 8 * lcm(*range(1, 65)); rnd = random.Random(33)
def dead(S, D): return any(d % (8 * D) == 0 for d in S)
members = []; tried = 0
while tried < 4000 and len(members) < 40:
    d1 = L * rnd.randrange(1, 20); lo = int(d1 / 8.9) + 1
    m = rnd.randrange(1, 4)
    rest = [8 * rnd.randrange(lo // 8 + 1, d1 // 8) for _ in range(m)] + [rnd.randrange(lo, d1) for _ in range(5 - m)]
    S = tuple(sorted([d1, lo + rnd.randrange(0, 3)] + rest)); tried += 1
    if len(set(S)) < 7 or max(S) >= 9 * min(S): continue
    if residual(S): members.append(S)
print(f"constructed {tried}: residual members with max/min < 9: {len(members)}")
Ds = Counter(); L0s = Counter(); worst = None
for S in members:
    D = 65; L0 = None
    while D <= 20000:
        if not dead(S, D):
            if L0 is None: L0 = D
            if any(clears(S, D, 8 * j + 1) for j in range(D)): break
        D += 1
    Ds[D] += 1; L0s[L0] += 1
    if worst is None or D > worst[0]: worst = (D, L0, S)
if members:
    print(f"first live lattice L_0: {sorted(L0s.items())}")
    print(f"least clearing D (cap 20000): {sorted(Ds.items())}")
    print(f"worst: D*={worst[0]}, L_0={worst[1]}, residues mod 8 of the set: {[d % 8 for d in worst[2]]}")
