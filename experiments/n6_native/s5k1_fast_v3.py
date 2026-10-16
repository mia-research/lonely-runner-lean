#!/usr/bin/env python3
"""Uniform arcs in the good set G (s5k1_fast_v2): A4 = {phi4 : (phi4, phi5) in G for every phi5} and
A5 = {phi5 : ... for every phi4}; their longest circular arcs, over a grid of (P, beta, gamma)."""
exec(open("s5k1_fast_v2.py").read().split("def study(")[0])
def longest(row):
    if all(row): return 1.0
    best = run = 0
    for x in row + row:
        run = run + 1 if x else 0; best = max(best, run)
    return min(best, N) / N
rows = []
for P in (1 / 6, 0.2, 0.25, 0.3, 1 / 3):
    for be in (0.02, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5):
        for ga in (be + 0.01, be + 0.1, 0.5, 1.0, 2.0, 5.0):
            if ga <= be: continue
            G = [[section_y(P, be, ga, i / N, k / N) for i in range(N)] for k in range(N)]
            A4 = [all(G[k][i] for k in range(N)) for i in range(N)]
            A5 = [all(G[k][i] for i in range(N)) for k in range(N)]
            rows.append((round(P, 3), be, round(ga, 3), longest(A4), longest(A5)))
print("P, beta, gamma, longest uniform phi4-arc (good for all phi5), longest uniform phi5-arc:")
for r in rows: print("  ", r)
