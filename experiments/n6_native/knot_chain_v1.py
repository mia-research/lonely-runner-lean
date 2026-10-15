#!/usr/bin/env python3
"""Observation only; follow-up to knot_displace_v1. At a death, push the knot forward: start from m + e_J; while some
pair (i, j) fails, (6 m_i + 1) v_j > (6 m_j + 5) v_i (i enters after j exits), give j one more lap. Each such step is a
further knot. Recorded: the chain length (knots after the first), whether the chain ends at the next lonely instant's
lap vector N (E66), and whether any step of the chain needed two runners at equal speed (no: speeds are distinct on
these paths, checked)."""
import sys
from fractions import Fraction as F
from collections import Counter
import importlib.util
sp = importlib.util.spec_from_file_location("sd", "slot_deform_v1.py"); sd = importlib.util.module_from_spec(sp); sp.loader.exec_module(sd)
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
STEP = int(sys.argv[1]) if len(sys.argv) > 1 else 4
def casc_from(v, t):
    while True:
        nxt = [F(6 * round(d * t) + 1, 6 * d) for d in v if abs(d * t - round(d * t)) < F(1, 6)]
        if not nxt: return t
        t = max(nxt)
def flanks(v, m):
    ent = [(F(6 * m[i] + 1, 6) / v[i], i) for i in range(5)]; ex = [(F(6 * m[i] + 5, 6) / v[i], i) for i in range(5)]
    L = max(ent)[0]; R = min(ex)[0]
    return [i for x, i in ent if x == L], [i for x, i in ex if x == R]
length = Counter(); endN = Counter(); distinct = 0; n = 0
for S in rows[::STEP]:
    R = sd.run_path(S, Counter(), Counter())
    for (m, a, hi), _ in zip(R["segs"], R["segs"][1:]):
        if hi == 0: continue
        v = sd.vs(S, hi); Is, Js = flanks(v, m)
        if len(Is) != 1 or len(Js) != 1: continue
        n += 1; distinct += len(set(v)) == 5
        k = list(m); k[Js[0]] += 1; steps = 0
        while True:
            bad = [(i, j) for i in range(5) for j in range(5) if i != j and (6 * k[i] + 1) * v[j] > (6 * k[j] + 5) * v[i]]
            if not bad: break
            for j in sorted(set(j for _, j in bad)): k[j] += 1
            steps += 1
        length[steps] += 1
        vn = sd.vs(S, hi + sd.EPS); N = casc_from(vn, sd.Lm(v, m))
        endN[("terminates (box non-empty by the pair criterion)", "equals next isolation N" if tuple(k) == sd.laps(vn, N) else "differs from N")] += 1
print(f"deaths (single flanks) on every {STEP}th path: {n}; speeds pairwise distinct at the death: {distinct}")
print("further knots in the forward chain (rounds after m + e_J):", dict(sorted(length.items())))
print("chain end:", dict(endN))
