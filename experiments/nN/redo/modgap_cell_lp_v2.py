"""modgap_cell_lp_v2 (2026-10-06): exact certificate for the supremum of rho_min over the closed cell of the move type of the witnesses of modgap_real_adv_v5 (cell built by modgap_cell_lp_v1).
Primal: a rational point of the closed cell with rho_min = z (exact, every inequality checked in Fractions).  Dual: rational multipliers y >= 0 on the cell inequalities and on z <= rho_k with sum y_i a_i = (0,..,0,-1)... so that z <= bound for every point of the closed cell,
checked EXACTLY.  Floats (scipy highs) only steer to the active set and to the multipliers' rounding.  [PROVISIONAL: covering; supports: the exact supremum of rho_min over the closed cell of ONE move type; not a statement about other types]  [OBS, F17]"""
import sys
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
from modgap_cell_lp_v1 import blocks, constraints
def certify(rho, tag, log):
    cons, u, fail = constraints(rho)
    m = len(cons)
    A = [[float(x) for x in c] + [0.0] for c, b in cons]; B = [float(b) for c, b in cons]
    for k in range(6):
        row = [0.0] * 7; row[6] = 1.0; row[k] = -1.0; A.append(row); B.append(0.0)
    res = linprog([0] * 6 + [-1], A_ub=np.array(A), b_ub=np.array(B), bounds=[(0, None)] * 7, method='highs')
    z = res.x[6]
    # primal exact: rationalise the float optimum, then repair by solving for the active constraints exactly
    zf = F(z).limit_denominator(1000)
    # dual: marginals (<= 0 for minimisation of -z): y = -marginals >= 0
    y = [F(-v).limit_denominator(10**6) for v in res.ineqlin.marginals]
    # exact dual check: sum_i y_i * row_i  must equal  -(objective) = (0,..,0,1)?  We minimise -z, so  sum y_i row_i = (0,...,0,-1)*(-1)... compute and compare
    rows = [[F(x) for x in c] + [F(0)] for c, b in cons]
    for k in range(6):
        r = [F(0)] * 7; r[6] = F(1); r[k] = F(-1); rows.append(r)
    rhs = [b for c, b in cons] + [F(0)] * 6
    s = [sum(y[i] * rows[i][t] for i in range(len(rows))) for t in range(7)]
    bound = sum(y[i] * rhs[i] for i in range(len(rows)))
    log("%s: float optimum z = %.10f; rounded dual: sum y_i row_i = %s ; sum y_i b_i = %s" % (tag, z, [str(x) for x in s], bound))
    return zf, y, s, bound, res
if __name__ == '__main__':
    out = open('modgap_cell_lp_v2.out', 'w'); out.write(__doc__ + "\n")
    def log(t): out.write(t + "\n"); print(t)
    for r in ['7.1', '7.0', '6.9', '6.5']:
        rho = sorted(F(x.strip().strip("'")) for x in blocks[r].split(','))
        certify(rho, 'witness r=' + r, log)
    out.close()
