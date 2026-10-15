#!/usr/bin/env python3
"""The 13 largest-flank exceptions (six_largest_flank_v2_150.out). For each: e, E = e/6 when 6 | e, and for
every opening j < e of the largest flank the elements that block it (residue d(6j+1) mod 6e outside [e,5e]).
For e = 6E with e the unique multiple of 6: the fine positions i < E, the cell vectors a(i), and whether
each lies in the bad set B (cell_criterion: then every coarse shift u is blocked). Reports which element
blocks most openings and whether a single element blocks a whole residue class of openings."""
from collections import Counter
from itertools import product
exc = [tuple(map(int, l.split()[1:6])) for l in open("six_largest_flank_v2_150.out") if l.startswith("FAIL")]
def blockers(S, e, j):
    m = 6 * j + 1
    return tuple(d for d in S[:-1] if not (e <= (d * m) % (6 * e) <= 5 * e))
def good(a, s): return any(all((a[t] + s[t] * u) % 6 not in (0, 5) for t in range(4)) for u in range(6))
for S in exc:
    e = S[-1]
    table = [blockers(S, e, j) for j in range(e)]
    cnt = Counter(d for b in table for d in b)
    single = Counter(b[0] for b in table if len(b) == 1)
    line = f"{S}: e={e}, openings blocked by exactly one element: {sum(1 for b in table if len(b) == 1)} of {e}; " \
           f"block counts per element {dict(cnt)}; sole blocker counts {dict(single)}"
    print(line)
    if e % 6 == 0 and sum(d % 6 == 0 for d in S) == 1:
        E = e // 6; rest = S[:-1]; s = tuple(d % 6 for d in rest); q = tuple(d // 6 for d in rest)
        cells = [tuple(((d * i + qq) % (6 * E)) // E for d, qq in zip(rest, q)) for i in range(E)]
        print(f"    e = 6E with E = {E}: residues mod 6 {s}; fine cell vectors {cells}; all in bad set: {all(not good(a, s) for a in cells)}")
    else:
        print(f"    e not the unique multiple of 6 (gcd(e,6) = {__import__('math').gcd(e, 6)}); openings and blockers: {table}")
