"""Residual members that the block split does not reach.

One runner d = L*u (L = 8*lcm(1..64)) kills every lattice D <= 64; a second large runner d' in
(d/7, d), chosen so gcd(d, d') is small, stops R8 and leaves no block with a large common factor.
Five small runners from [1,100].  For each member: is there a certificate at a SMALL flank
(an opening (j + 1/8)/e with e in the core, j < e) -- exact integer band test?  If not, at which
flank does the first lonely opening sit?
"""
exec(open('residual_members_v1.py').read().split("L = 8 * lcm")[0])
from math import lcm
L = 8 * lcm(*range(1, 65)); rnd = random.Random(31)
def band(S, e, j): return all(e <= d * (8 * j + 1) % (8 * e) <= 7 * e for d in S)
members = []; tried = 0
while tried < 3000:
    C = rnd.sample(range(1, 101), 5); d = L * rnd.randrange(1, 50)
    d2 = rnd.randrange(d // 7 + 1, d)
    S = tuple(sorted(C + [d, d2])); tried += 1
    if math.gcd(d, d2) > 10**6: continue
    if residual(S): members.append(S)
print(f"constructed {tried}: residual members with gcd(d, d') <= 10^6: {len(members)}")
small = 0; flank_of = Counter() if False else {}
from collections import Counter
where = Counter(); ex = []
for S in members:
    core = [x for x in S if x < 10**6]
    hit = next(((e, j) for e in core for j in range(e) if band(S, e, j)), None)
    if hit: small += 1; where['core flank'] += 1
    else:
        where['no core-flank certificate'] += 1
        if len(ex) < 3: ex.append(S)
print(f"certificate at a core flank (e <= 100, j < e): {small}/{len(members)};  {dict(where)}")
for S in ex: print("   no core-flank certificate:", [x for x in S if x < 10**6], "+ two large")
