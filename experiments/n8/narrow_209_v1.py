"""E950: the crossers whose narrowest island (among non-closer readings, island_vs_pass_v1) is class N (E947: 209).  Exact.
For each: the narrowest reading's class, whether its island reaches a pass interval on the escape side (need <= extent,
E949 item 2), and the class of the slowest attaining reading of the crosser (crosser_equality_v1)."""
import pickle, glob
from fractions import Fraction as Fr
from collections import Counter, defaultdict
out = []
for f in sorted(glob.glob('island_vs_pass_v1_part*.pkl')): out += pickle.load(open(f, 'rb'))
rows = []
for f in sorted(glob.glob('crosser_equality_v1_part*.pkl')): rows += pickle.load(open(f, 'rb'))
att = {r[0]: (r[4], r[3]) for r in rows}
by = defaultdict(list)
for o in out: by[o[0]].append(o)
c = Counter()
for idx, lst in by.items():
    w = min(lst, key=lambda o: (o[6] - o[5]) / o[4]); _, k, kc, role, v0, L_, R_, a, b, P = w
    if kc != 'N': c[('narrowest island class', kc)] += 1; continue
    left = [(l, h, m) for l, h, m in P if h <= v0]; right = [(l, h, m) for l, h, m in P if l >= v0]
    nL = (v0 - max(left)[1]) / v0 if left else None; nR = (min(right)[0] - v0) / v0 if right else None
    reach = (nL is not None and nL <= (v0 - L_) / v0) or (nR is not None and nR <= (R_ - v0) / v0)
    A_, cl = att[idx]
    c[('narrowest island class N', 'reaches a pass interval', reach, 'reading', k, 'slowest attaining reading class', cl[min(A_)])] += 1
    c[('narrowest island class N', 'total')] += 1
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
