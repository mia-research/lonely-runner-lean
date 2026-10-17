#!/usr/bin/env python3
"""Level-2 grid failures as residue patterns (EXACT, complete).  A pattern is a multiset of r units mod 49 (r = 4, 5);
it FAILS level 2 if no unit k mod 49 has every u k mod 49 in [7, 42] (multiples of 7 are automatic at level 2).
Enumerates all multisets up to multiplication by a common unit (orbit representative = lexicographically least
scaled sorted tuple), lists the failing orbits for r = 4 and r = 5, and checks that every failing r = 5 pattern contains
a failing r = 4 sub-pattern or not."""
from itertools import combinations_with_replacement
from collections import Counter
U = [u for u in range(1, 49) if u % 7]
good_k = {}
def ok(pat):
    return any(all(7 <= (u * k) % 49 <= 42 for u in pat) for k in U)
def canon(pat):
    return min(tuple(sorted((u * c) % 49 for u in pat)) for c in U)
for r in (3, 4, 5):
    seen = set(); fails = []
    for pat in combinations_with_replacement(U, r):
        cp = canon(pat)
        if cp in seen: continue
        seen.add(cp)
        if not ok(cp): fails.append(cp)
    print(f"r = {r}: orbits {len(seen)}, failing level 2: {len(fails)}")
    if r <= 4: print("   failing orbits:", fails)
    else:
        print("   failing orbits (first 40):", fails[:40])
        f4 = set()
        for p in fails:
            subs = {canon(q) for q in combinations_with_replacement(p, 4) if Counter(q) <= Counter(p)}
            f4.add(any(not ok(s) for s in subs))
        print("   every failing r=5 orbit contains a failing r=4 sub-orbit:", f4)
    open(f"seven_mod49_fail_r{r}.txt", "w").write("\n".join(map(str, fails)) + "\n")
