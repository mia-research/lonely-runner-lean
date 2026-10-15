#!/usr/bin/env python3
"""Structure of the bad cell set B_s = (Z/6)^4 minus G_s for the residue patterns forced in the
divisible-largest case (s a permutation of (1,2,3,5) or (1,3,4,5)). Tests: is B a graph over three
coordinates (each triple extends uniquely)?  Lists B for the sorted patterns, compressed."""
from itertools import product
from collections import Counter
def bad(s):
    return [a for a in product(range(6), repeat=4)
            if not any(all((a[t] + s[t] * u) % 6 not in (0, 5) for t in range(4)) for u in range(6))]
for s in [(1, 2, 3, 5), (1, 3, 4, 5)]:
    B = bad(s)
    print(f"residues s={s}: |B|={len(B)}")
    for drop in range(4):
        keys = Counter(tuple(a[t] for t in range(4) if t != drop) for a in B)
        print(f"  graph over coords without #{drop} (residue {s[drop]}): distinct triples={len(keys)}, max fibre={max(keys.values())}")
    # per-coordinate value distribution
    for t in range(4):
        print(f"  coord {t} (s={s[t]}): values {dict(sorted(Counter(a[t] for a in B).items()))}")
    # test linear relations sum c_t a_t = const mod 6 holding on all of B? (count best)
    best = []
    for c in product(range(6), repeat=4):
        if c == (0,0,0,0): continue
        vals = Counter(sum(ct*at for ct, at in zip(c, a)) % 6 for a in B)
        best.append((len(vals), c, dict(vals)))
    best.sort()
    print("  linear forms with fewest values on B:", best[:3])
