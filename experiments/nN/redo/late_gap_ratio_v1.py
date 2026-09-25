"""Late events (past the first lap) against the arrangement's consecutive speed gaps (owner, 2026-09-26: "any
arrangement is dealt with by d_min / d_max in the first lap except where two runners are close together").
For every late event on file: rho = g_max / g_min of the seven consecutive speed gaps, and whether the subject is an
endpoint of the smallest gap.  Exact.  Output: late_gap_ratio_v1.out."""
import re, ast
from fractions import Fraction as F
from math import floor
from arrangement_lib import readings, nd
def cascade(ds):
    t = F(1, 8 * min(ds))
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)
cases = []
for line in open('late_event_S9_search_v1.out'):
    m = re.search(r'LATE seed \d+: .* V=(\[[^\]]*\]) subject (\d+)', line)
    if m: cases.append((sorted(ast.literal_eval(m.group(1))), int(m.group(2))))
for line in open('late_S9_witness_v1.out'):
    m = re.search(r'speeds (\[[^\]]*\])', line)
    if m: V = ast.literal_eval(m.group(1)); cases.append((sorted(V), V[0]))
cases += [([27,70,107,137,159,188,344,393], 393), ([1,31,75,97,128,160,176,225], 1),
          ([1,1975,5265,6910,8737,9589,11845,15135], 1), ([109,154,234,273,313,337,390,469], 109)]
rows = []
for V, s in cases:
    ds = readings(V, V.index(s)); u = min(ds) * cascade(ds)
    if u <= F(7, 8): continue
    g = [b - a for a, b in zip(V, V[1:])]; rho = F(max(g), min(g)); i = g.index(min(g))
    rows.append((rho, s in (V[i], V[i + 1]), V.index(s) + 1))
rows.sort()
print(f"late events {len(rows)}; min gap ratio {rows[0][0]}; subject an endpoint of the smallest gap: {sum(r[1] for r in rows)}")
