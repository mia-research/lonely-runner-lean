#!/usr/bin/env python3
"""Exceptions of seven_cells_v1 (EXACT): for each, which runners' flanks carry a lonely opening (residue criterion over
all openings j of that flank, entry 7j+1 and exit 7j+6), and for the fastest runner v6 the classes of j mod 7 that
work.  Tests whether the fastest runner's flank always carries a lonely opening."""
import ast, sys
from collections import Counter
exc = [ast.literal_eval(l) for l in open(sys.argv[1]) if l.strip()]
def lonely(S, e, r):  # instant r/(7e)
    m = 7 * e
    return all(e <= (d * r) % m <= 6 * e for d in S)
carry = Counter(); v6ok = 0; jcls = Counter(); none6 = []
for S in exc:
    ranks = []
    for i, e in enumerate(S):
        if any(lonely(S, e, 7 * j + 1) or lonely(S, e, 7 * j + 6) for j in range(e)): ranks.append(i + 1)
    carry[tuple(ranks)] += 1
    e = S[5]; js = [j for j in range(e) if lonely(S, e, 7 * j + 1)]
    if js or any(lonely(S, e, 7 * j + 6) for j in range(e)): v6ok += 1
    else: none6.append(S)
    for j in js[:1]: jcls[(j % 7, e % 7)] += 1
print(f"{len(exc)} exceptions; fastest runner's flank carries a lonely opening in {v6ok}")
print("  flanks (ranks) carrying a lonely opening:", carry.most_common(12))
print("  first lonely entry opening of v6: (j mod 7, v6 mod 7):", sorted(jcls.items())[:30])
print("  exceptions where v6's flank carries none (first 15):", none6[:15], len(none6))
