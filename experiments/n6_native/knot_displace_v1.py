#!/usr/bin/env python3
"""Observation only. Owner: a death is not a handover but a displacement - the knot that closes one isolation is an
opening elsewhere; two knots would need equal speeds.
At a death on the AP -> SixResidual lines the dying box m is one point t*: runner I reads exactly 1/6 (entry flank,
lap m_I) and runner J exactly 5/6 (exit flank, lap m_J). The knot is the pair (I, J) tight: (6 m_I + 1) v_J = (6 m_J + 5) v_I.
Its two sides: forward, J leaves and re-enters on its next lap -> box m + e_J (J the new entry flank);
backward, I steps back to its previous exit -> box m - e_I (I the new exit flank).
Recorded at the death s: whether m + e_J and m - e_I are alive (non-empty lap box); when not, which pairs fail there
(the 'second knot'); and the pairwise check for (I, J) alone in m + e_J."""
import sys
from fractions import Fraction as F
from collections import Counter
import importlib.util
sp = importlib.util.spec_from_file_location("sd", "slot_deform_v1.py"); sd = importlib.util.module_from_spec(sp); sp.loader.exec_module(sd)
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
STEP = int(sys.argv[1]) if len(sys.argv) > 1 else 4
def fails(v, m):
    if min(m) < 0: return [("neg",)]
    return [(i, j) for i in range(5) for j in range(5) if i != j and (6 * m[i] + 1) * v[j] > (6 * m[j] + 5) * v[i]]
def flanks(v, m):
    ent = [(F(6 * m[i] + 1, 6) / v[i], i) for i in range(5)]; ex = [(F(6 * m[i] + 5, 6) / v[i], i) for i in range(5)]
    L = max(ent)[0]; R = min(ex)[0]
    return [i for x, i in ent if x == L], [i for x, i in ex if x == R]
res = Counter(); second = Counter(); pairIJ = Counter(); n = 0; ex = []
for S in rows[::STEP]:
    R = sd.run_path(S, Counter(), Counter())
    for (m, a, hi), _ in zip(R["segs"], R["segs"][1:]):
        if hi == 0: continue
        v = sd.vs(S, hi); Is, Js = flanks(v, m)
        if len(Is) != 1 or len(Js) != 1: res["tied flanks (skipped)"] += 1; continue
        I, J = Is[0], Js[0]; n += 1
        fw = list(m); fw[J] += 1; bw = list(m); bw[I] -= 1
        ff, fb = fails(v, fw), fails(v, bw)
        res[("forward m+e_J alive" if not ff else "forward dead", "backward m-e_I alive" if not fb else "backward dead")] += 1
        pairIJ[not any(set(p) == {I, J} for p in ff)] += 1
        if ff and fb:
            role = lambda x: "I" if x == I else "J" if x == J else "O"
            second[(tuple(sorted(set((role(p[0]), role(p[1])) for p in ff if p != ("neg",)))),
                    tuple(sorted(set((role(p[0]), role(p[1])) if p != ("neg",) else ("neg",) for p in fb))))] += 1
            if len(ex) < 4: ex.append((S, hi, m, I + 1, J + 1, ff, fb))
print(f"deaths (single flanks) on every {STEP}th path: {n}")
for k, c in res.most_common(): print(f"  {c:6d}  {k}")
print("in m+e_J, the pair (I,J) itself is satisfied:", dict(pairIJ))
print("both sides dead - failing pairs by role (forward ; backward), commonest:")
for k, c in second.most_common(10): print(f"  {c:6d}  {k}")
for e in ex: print("  example:", e)
