#!/usr/bin/env python3
"""Observation only. Owner: are there a few native kinds of the way a speed deformation moves an isolation?
Deaths after s = 0 on the AP -> SixResidual straight lines (slot_deform_v1 segments, every STEP-th set). At a death the
dying box is one point: its entry flank i (binding (m_i+1/6)/v_i) meets its exit flank j (binding (m_j+5/6)/v_j).
The isolation moves to the next lonely instant (alive at the death, E66). Each relocation is described only by roles:
  - the new entry flank and new exit flank, as: I (old entry flank), J (old exit flank), O (another runner);
  - which roles gain laps (lap change N - m restricted to I, J, O; with the size of the gain);
  - speed order of I and J (I faster or slower than J).
Counts the distinct role-kinds and lists them."""
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
kinds = Counter(); n = 0; multi = 0
for S in rows[::STEP]:
    R = sd.run_path(S, Counter(), Counter())
    for (m, a, hi), _ in zip(R["segs"], R["segs"][1:]):
        if hi == 0: continue
        v = sd.vs(S, hi); I, J = flanks(v, m)
        if len(I) != 1 or len(J) != 1: multi += 1; continue
        I, J = I[0], J[0]; n += 1
        vn = sd.vs(S, hi + sd.EPS); N = casc_from(vn, sd.Lm(v, m)); mN = sd.laps(vn, N)
        I2, J2 = flanks(v, mN)
        role = lambda x: "I" if x == I else "J" if x == J else "O"
        gain = tuple(sorted((role(k), mN[k] - m[k]) for k in range(5) if mN[k] != m[k]))
        key = ("I faster" if v[I] > v[J] else "J faster",
               "entry " + "/".join(sorted(set(role(x) for x in I2))), "exit " + "/".join(sorted(set(role(x) for x in J2))), gain)
        kinds[key] += 1
print(f"deaths with a single entry and exit flank: {n} (ties skipped: {multi}); distinct role-kinds: {len(kinds)}")
cum = 0
for k, c in kinds.most_common(40):
    cum += c; print(f"  {c:6d}  cum {cum / n:.3f}  {k}")
