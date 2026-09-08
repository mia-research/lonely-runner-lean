r"""
ob_torus_id_v1 -- is  o (over x in [0,1))  ==  o (over the full torus theta in [0,1)) ?

If yes, o is a genuine Weyl box-average of the closed geodesic theta -> (e_rho theta)
on T^4, which is what makes the Fourier machinery applicable.  Exhaustive, exact.
"""
import sys, itertools
from functools import reduce
from math import gcd
from ob_core_v1 import o_x, o_torus, primitive_tuples, audit_x, audit_torus

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 4
n = 0
bad = []
for e in primitive_tuples(QMAX):
    n += 1
    a, b = o_x(e), o_torus(e)
    if a != b:
        bad.append((e, a, b))
print(f"primitive unit 4-tuples with q <= {QMAX}: {n}")
print(f"   o_x != o_torus : {len(bad)}")
for e, a, b in bad[:20]:
    print("     ", e, a, b)

# boundary audit on the whole sweep (requirement (i)), both grids
ci = cm = cells = 0
tci = tcm = tcells = 0
for e in itertools.islice(primitive_tuples(QMAX), 0, 400):
    c, i, m = audit_x(e); cells += c; ci += i; cm += m
    c, i, m = audit_torus(e); tcells += c; tci += i; tcm += m
print(f"   boundary audit (first 400 tuples): x-grid cells={cells} interior-bp={ci} entry!=exit={cm}")
print(f"                                      theta-grid cells={tcells} interior-bp={tci} entry!=exit={tcm}")
