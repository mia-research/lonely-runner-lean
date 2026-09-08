r"""du2_report_tables_v1 -- the tables printed into reports/n8_dropped_unit.md."""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import importlib.util
spec = importlib.util.spec_from_file_location(
    "ne", "/Users/trentpalelei/Desktop/Math Ex/experiments/n8/du2_nonrep_endtoend_v1.py")
ne = importlib.util.module_from_spec(spec); spec.loader.exec_module(ne)
Z8 = frozenset(range(8)); UNITS = {1, 3, 5, 7}
pairs = [A for A in combinations(range(1, 8), 2) if set(A) & UNITS]

def windows(Enon):
    cells = ne.safe_cells(Enon); w = []
    for a, b, U in cells:
        if w and w[-1][1] == a: w[-1][1] = b; w[-1][2].append(U)
        else: w.append([a, b, [U]])
    return [(lo, hi, frozenset.intersection(*Us)) for lo, hi, Us in w]

print("TABLE 1  exact safe set of the five representative non-divisible runners\n")
print("| absent | E_non | \\|S\\| | float | \\|S\\|-1/2 | windows (length; residues valid throughout) |")
print("|---|---|---|---|---|---|")
for A in pairs:
    E = sorted(set(range(1, 8)) - set(A))
    w = windows(E)
    m = sum((hi - lo for lo, hi, _ in w), F(0))
    ws = "; ".join(f"`[{lo},{hi})` len `{hi-lo}` "
                   f"{sorted(c) if c else 'mixed'}" for lo, hi, c in w)
    print(f"| {A} | {E} | `{m}` | {float(m):.5f} | `{m-F(1,2)}` | {ws} |")

print("\n\nTABLE 2  one explicit witness per absent pair, m1=1, m2=2 "
      "(E = E_non u {8,16}, N = 8L)\n")
print("| absent | E | L | b | r | k | min_e \\|\\|ek/N\\|\\| |")
print("|---|---|---|---|---|---|---|")
for A in pairs:
    E = sorted(set(range(1, 8)) - set(A))
    d = ne.run(E, 1, 2)
    assert d['ok']
    print(f"| {A} | {d['E']} | {d['L']} | {d['b']} | {d['r']} | {d['k']} | `{d['slack']}` |")

print("\n\nTABLE 3  the extremal pair (3,4): S and the worst divisible pair\n")
E = [1, 2, 5, 6, 7]
for lo, hi, c in windows(E):
    print(f"  window [{lo},{hi})  length {hi-lo}  residues valid throughout: {sorted(c) if c else 'none common'}")
worst = None
for m1 in range(1, 41):
    for m2 in range(m1 + 1, 41):
        u = ne.meas(ne.merge(ne.Bm_clip(m1) + ne.Bm_clip(m2)))
        if worst is None or u > worst[0]: worst = (u, m1, m2)
print(f"  max |B_m1 u B_m2| over 1<=m1<m2<=40 = {worst[0]} = {float(worst[0]):.6f} "
      f"at (m1,m2) = ({worst[1]},{worst[2]})")
print(f"  19/35 - 1/2 = {F(19,35)-F(1,2)};  19/35 - {worst[0]} = {F(19,35)-worst[0]} "
      f"= {float(F(19,35)-worst[0]):.6f}")
