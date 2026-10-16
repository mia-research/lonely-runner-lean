#!/usr/bin/env python3
"""Check of APFold_v1.knot_other_side against the E68 deaths: the knotted pair (I,J) holds in m + e_J iff
2 m_I <= 4 m_J + 3 (n = 6). Every 4th AP -> SixResidual path, single-flank deaths."""
import sys
from fractions import Fraction as F
from collections import Counter
import importlib.util
sp = importlib.util.spec_from_file_location("sd", "slot_deform_v1.py"); sd = importlib.util.module_from_spec(sp); sp.loader.exec_module(sd)
def flanks(v, m):
    ent = [(F(6 * m[i] + 1, 6) / v[i], i) for i in range(5)]; ex = [(F(6 * m[i] + 5, 6) / v[i], i) for i in range(5)]
    L = max(ent)[0]; R = min(ex)[0]
    return [i for x, i in ent if x == L], [i for x, i in ex if x == R]
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
agree = Counter()
for S in rows[::4]:
    R = sd.run_path(S, Counter(), Counter())
    for (m, a, hi), _ in zip(R["segs"], R["segs"][1:]):
        if hi == 0: continue
        v = sd.vs(S, hi); Is, Js = flanks(v, m)
        if len(Is) != 1 or len(Js) != 1: continue
        I, J = Is[0], Js[0]; fw = list(m); fw[J] += 1
        holds = (6 * fw[J] + 1) * v[I] <= (6 * fw[I] + 5) * v[J] and (6 * fw[I] + 1) * v[J] <= (6 * fw[J] + 5) * v[I]
        agree[holds == (2 * m[I] <= 4 * m[J] + 3)] += 1
print("pair (I,J) in m + e_J holds  <->  2 m_I <= 4 m_J + 3:", dict(agree))
