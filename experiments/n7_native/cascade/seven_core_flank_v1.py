#!/usr/bin/env python3
"""Core sets (seven_core_v1, EXACT): which flanks carry a lonely opening; for the fastest runner e (if coprime to 7) the
lonely openings in coprime-flank form: x = (7j+1) mod e (entry) or (7j+6) mod e (exit), with t = (7j+1)/(7e), and for
the multiple of 7 m: its lap floor(m t) and its reading class.  Looks for the simplest lonely x."""
import ast, sys, math
from fractions import Fraction as F
from collections import Counter
core = [ast.literal_eval(l) for l in open(sys.argv[1]) if l.strip()]
def lon(S, e, r):
    m = 7 * e
    return all(e <= (d * r) % m <= 6 * e for d in S)
carry = Counter(); v6c = Counter(); ex = []; jmin = Counter(); notv6 = []
for S in core:
    fl = tuple(i + 1 for i, e in enumerate(S) if any(lon(S, e, 7 * j + 1) or lon(S, e, 7 * j + 6) for j in range(e)))
    carry[fl] += 1
    e = S[5]
    js = [(7 * j + 1, j) for j in range(e) if lon(S, e, 7 * j + 1)] + [(7 * j + 6, j) for j in range(e) if lon(S, e, 7 * j + 6)]
    if not js: notv6.append(S); continue
    r, j = min(js)
    jmin[min(j, 10)] += 1
    if len(ex) < 15: ex.append((S, f"{r}/{7*e}", j))
print(f"{len(core)} core sets")
print("  flanks carrying a lonely opening (ranks):", carry.most_common(10))
print("  fastest runner carries none:", len(notv6), notv6[:12])
print("  earliest lonely opening of the fastest runner, lap j (capped 10):", sorted(jmin.items()))
print("  examples (set, earliest lonely instant of v6, its lap):", ex)
