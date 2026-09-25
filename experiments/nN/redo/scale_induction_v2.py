"""Step(j) with later cells allowed (scale_induction_v1: 8 of 9,604 steps land beyond U_{j-1}'s first
positive cell, all because that cell is ~1e-7 wide).  For every step: the index of the lonely cell of
U_{j-1} (counting only cells of positive length, from tau_{j-1}) in which tau_j lands (0 = at
tau_{j-1} itself), and the widths of the cells passed over, in turns of level j's slowest reading.
Same arrangements and seed as v1; exact."""
import random
from collections import Counter
from fractions import Fraction as F
from arrangement_lib import readings, nd
from isolated_persistence_v1 import cascade_cap
from nested_cascade_v1 import cascade_from
from scale_induction_v1 import levels, cell_end, first_positive_cell
import separation_arrangements_v1 as SA
rnd = random.Random(57); SA.rnd = rnd
exec(open('scale_induction_v1.py').read().split("    def multilevel():")[1].split("    fams = {")[0].replace("\n        ", "\n").replace("        # 3-4", "# 3-4").join(["def multilevel():", ""]) if False else "")
import scale_induction_v1 as SI
src = open('scale_induction_v1.py').read()
ml = src[src.index("    def multilevel():"):src.index("    fams = {")]
exec("\n".join(l[4:] for l in ml.split("\n")))
fams = {n: (lambda n=n: SA.family(n)) for n in ("uniform", "clustered", "slow-plus-fast")}
fams["multi-level"] = multilevel
idx = Counter(); skipped_w = []
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
                if tj == tprev: idx[0] += 1; continue
                s, n = tprev, 0
                while True:
                    s, e = first_positive_cell(prev, s); n += 1
                    if s <= tj <= e: break
                    skipped_w.append(float((e - s) * min(L)))
                    s = cascade_from(prev, e + F(1, 10**15))
                idx[n] += 1
print(f"steps: {sum(idx.values())};  index of the U_(j-1) cell where level j lands (0 = at tau_(j-1)): {dict(sorted(idx.items()))}")
if skipped_w: print(f"   cells passed over: {len(skipped_w)}; their widths in turns of level j's slowest reading: max {max(skipped_w):.4f}, all < 1: {all(w < 1 for w in skipped_w)}")
