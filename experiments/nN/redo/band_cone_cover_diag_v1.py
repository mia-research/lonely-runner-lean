"""E124 diagnosis: rerun the wall-cut recursion for a few waves and record, for the pieces in the frontier, the interior
slack tau (0 = no interior: a flat piece on a wall or on a tie s_i = s_{i+1})."""
import sys
from fractions import Fraction as F
from collections import Counter
from band_cone_cover_exact_v1 import BASE, load_cones, process, interior
cones = load_cones(); frontier = [BASE]
for wave in range(9):
    nxt = []
    for P in frontier:
        kind, k, ch, new = process((P, cones))
        for c in new:
            if c not in cones: cones.append(c)
        nxt += ch
    frontier = nxt
taus = Counter()
for P in frontier[:600]:
    x, t = interior(P)
    taus['empty' if t is None else ('flat (tau = 0)' if t == 0 else ('thin (tau < 1e-3)' if t < F(1, 1000) else 'fat'))] += 1
print("after 9 waves: frontier", len(frontier), "; first 600 pieces by interior slack:", dict(taus))
