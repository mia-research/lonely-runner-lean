"""WP3 item 2: the structure of the longest blocked stretches, read exactly.  For each top block: the stretch [a, b],
its expression in the slowest runner d1's laps (a*d1, b*d1), the slowest runner's zones inside it and hence how many of
its clear bands (length 3/(4 d1)) the other five bridge, and each runner's phase at the stretch's centre.  Exact."""
from fractions import Fraction as F
from math import floor
from block_extremal_v1 import comps
tops = [[165, 166, 337, 494, 505, 772], [355, 357, 373, 524, 561, 784], [232, 233, 361, 365, 680, 742],
        [186, 255, 280, 499, 565, 728], [395, 457, 470, 624, 634, 696], [165, 170, 265, 448, 535, 700]]
for B in tops:
    cs = comps(B); L, a, b = max(((q - p, p, q) for p, q in cs if p > 0))
    d1 = min(B); A, Bd = a * d1, b * d1
    # the slowest runner's zones (m - 1/8, m + 1/8) in lap units meeting [A, Bd]
    ms = [m for m in range(floor(A) - 1, floor(Bd) + 2) if m + F(1, 8) > A and m - F(1, 8) < Bd]
    bridged = max(0, len(ms) - 1)
    starts_on_d1 = (A - F(-1, 8)) % 1 == 0 or (A + F(1, 8)) % 1 == 0
    centre = (a + b) / 2
    phases = {d: (d * centre) % 1 for d in B}
    rel = {d: ((d - d1) * centre) % 1 for d in B}
    print(f"block {B}: L*d1 = {L*d1} ({float(L*d1):.4f});  stretch in d1-laps [{float(A):.4f}, {float(Bd):.4f}];"
          f" d1-zones inside at laps {ms} -> d1's clear bands bridged by the other five: {bridged}")
    print(f"      centre t = {centre} ({float(centre):.5f}); phase of each runner relative to the slowest at the centre:"
          f" {[f'{d}:{float(r):.3f}' for d, r in rel.items()]}")
