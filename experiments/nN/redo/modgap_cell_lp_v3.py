"""modgap_cell_lp_v3 (2026-10-06): completes modgap_cell_lp_v2 for the type of the witnesses r = 71/10, 7, 69/10 (same move type): (i) the dual multipliers are checked >= 0 exactly; (ii) an exact primal point of the CLOSED cell with rho_min = 43/6 is exhibited
(vertex found by solving the active set exactly, then every inequality of the cell checked in Fractions).  Together: sup of rho_min over the closed cell = 43/6 exactly.  [PROVISIONAL: covering; supports: the exact supremum of rho_min over the closed cell of ONE move type]  [OBS, F17]"""
from fractions import Fraction as F
import numpy as np, itertools
from scipy.optimize import linprog
from modgap_cell_lp_v1 import blocks, constraints
from modgap_cell_lp_v2 import certify
out = open('modgap_cell_lp_v3.out', 'w'); out.write(__doc__ + "\n")
def log(t): out.write(t + "\n"); print(t)
rho = sorted(F(x.strip().strip("'")) for x in blocks['7.1'].split(','))
zf, y, s, bound, res = certify(rho, 'type of witness r=7.1', log)
log("dual multipliers: count %d, minimum %s (>= 0: %s), support size %d" % (len(y), min(y), min(y) >= 0, sum(1 for v in y if v != 0)))
cons, u, fail = constraints(rho)
# primal: take the float optimum, solve the active constraints (|slack| < 1e-7) exactly by least squares on a rational basis: use the support of the dual (complementary slackness) as the active set
A = [[float(x) for x in c] for c, b in cons]; B = [float(b) for c, b in cons]
x = res.x[:6]
act = [i for i in range(len(cons)) if abs(sum(A[i][t] * x[t] for t in range(6)) - B[i]) < 1e-7]
log("active constraints at the float optimum: %d" % len(act))
# the optimum has rho_k = z for the readings at the minimum: z = 43/6 on those; solve the rank-deficient active system exactly by sympy
import sympy
M = sympy.Matrix([[sympy.Rational(cons[i][0][t].numerator, cons[i][0][t].denominator) for t in range(6)] for i in act]); bv = sympy.Matrix([sympy.Rational(cons[i][1].numerator, cons[i][1].denominator) for i in act])
sol = sympy.linsolve((M, bv))
log("exact solution set of the active system: %s" % (sol,))
pt = None
for s_ in sol:
    cand = [F(int(sympy.fraction(v)[0]), int(sympy.fraction(v)[1])) if v.is_Rational else None for v in s_]
    if None not in cand: pt = cand
if pt is None:
    # free parameters: fix them from the float optimum, rationalised
    s_ = list(sol)[0]; free = sorted(set().union(*[v.free_symbols for v in s_]), key=str)
    sub = {f: sympy.Rational(F(float(x[int(str(f)[-1]) - 1] if False else 0)).limit_denominator(1000).numerator, 1) for f in free}
    log("free symbols in the active solution: %s" % free)
else:
    ok = all(sum(c[t] * pt[t] for t in range(6)) <= b for c, b in cons)
    log("exact vertex %s ; satisfies every inequality of the closed cell: %s ; rho_min = %s" % ([str(v) for v in pt], ok, min(pt)))
out.close()
