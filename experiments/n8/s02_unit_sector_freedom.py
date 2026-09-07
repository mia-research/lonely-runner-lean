"""S02: with ACTUAL speeds e = 8q+rho (q>=0), the sector T_e = floor(e*b/L) mod 8
is what enters bad(). Question: over all (T_1,T_3,T_5,T_7) in (Z/8)^4, what
uncovered sets are achievable by the four unit runners alone?"""
from itertools import product
from n8_fibre_core import bad

achievable = {}
full = []
for T in product(range(8), repeat=4):
    blk = set()
    for rho, t in zip((1,3,5,7), T):
        blk |= bad(rho, t)
    unc = tuple(sorted(set(range(8)) - blk))
    achievable.setdefault(unc, []).append(T)
    if not unc:
        full.append(T)

print("number of (T1,T3,T5,T7) in (Z/8)^4 :", 8**4)
print("number giving FULL cover Z/8 by units alone :", len(full))
print("example full-cover sector vectors (T1,T3,T5,T7):", full[:8])
print()
print("distinct uncovered sets achievable by the 4 units, by size:")
for size in range(5):
    ss = sorted(u for u in achievable if len(u)==size)
    print(f"  |unc|={size}: {len(ss)} sets  {ss if size<=2 else ''}")
print()
# parity classification
mixed = {u:len(v) for u,v in achievable.items() if u and any(z%2 for z in u) and any(z%2==0 for z in u)}
print("MIXED-parity uncovered sets achievable and their multiplicity:")
for u,c in sorted(mixed.items()):
    print("   ", u, c)
print()
print("count of sector-vectors leaving uncovered EXACTLY {1,4}:", len(achievable.get((1,4),[])))
print("count of sector-vectors leaving uncovered EXACTLY {3,6}:", len(achievable.get((3,6),[])))
# which T vectors do the representative windows realise?
print()
print("representative window [2/7,2/5): (T1,T3,T5,T7) = (0,0,1,2) and (0,1,1,2)")
print("representative window [3/5,5/7): (T1,T3,T5,T7) = (0,1,3,4) and (0,2,3,4)")
