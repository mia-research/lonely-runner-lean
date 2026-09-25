"""Owner's hunch (2026-09-25): the narrow cells come from a ratio of speed differences to the AP ideal.
Identity: at a cell start tau = 1/(8D) (scale D), a reading c reads s/8 with s = c/D; it next enters its zone
at s = 8m+7, so the cell's width is min_c (8m+7 - s)/(8c): set by the reading whose ratio c/D falls just
SHORT of an AP value 8m+7 (the AP's 7/8 slot).  For the 8 narrow cells of scale_induction_v2: the reading
that ends the cell, its ratio s = c/D, the AP value it falls short of, and the shortfall."""
import random
from fractions import Fraction as F
from math import ceil
from arrangement_lib import readings
from isolated_persistence_v1 import cascade_cap
from nested_cascade_v1 import cascade_from
from scale_induction_v1 import levels, first_positive_cell
import separation_arrangements_v1 as SA
rnd = random.Random(57); SA.rnd = rnd
src = open('scale_induction_v1.py').read(); ml = src[src.index("    def multilevel():"):src.index("    fams = {")]
exec("\n".join(l[4:] for l in ml.split("\n")))
fams = {n: (lambda n=n: SA.family(n)) for n in ("uniform", "clustered", "slow-plus-fast")}; fams["multi-level"] = multilevel
for name, gen in fams.items():
    for _ in range(300):
        V = sorted(set(gen()))
        if len(V) < 8: continue
        for k in range(8):
            ds = readings(V, k); Ls = levels(ds)
            if len(Ls) < 2: continue
            U = []
            for j, L in enumerate(Ls):
                prev = list(U); U = U + L
                if j == 0: continue
                tprev, _ = cascade_cap(prev); tj, _ = cascade_cap(U)
                if tj == tprev: continue
                s0, e = first_positive_cell(prev, tprev)
                if s0 <= tj <= e: continue
                D = 1 / (8 * s0)
                ends = sorted(((ceil(c * s0 + F(1, 8)) - F(1, 8) - c * s0) / c, c) for c in prev)
                w, c = ends[0]; s = c / D; ap = ceil(s + 1) - 1 if (s % 8) else s
                target = 8 * ((s - 7) // 8 + (1 if (s - 7) % 8 else 0)) + 7 if False else None
                m7 = min((8 * m + 7 for m in range(0, int(s) // 8 + 2) if 8 * m + 7 >= s), default=None)
                print(f"{name}: levels {Ls}, step j={j}: cell starts at 1/(8D), D = {float(D):.4f}; width {float(w):.3e}; "
                      f"ended by reading {c}: c/D = {float(s):.5f}, AP value 8m+7 = {m7}, shortfall {float(m7 - s):.5f}")
