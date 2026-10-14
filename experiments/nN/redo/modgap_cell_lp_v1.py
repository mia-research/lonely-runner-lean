"""modgap_cell_lp_v1 (2026-10-06): the cell of the move type shared by the exact counterexamples of modgap_real_adv_v5, and the supremum of rho_min over its closure.
For a witness (six rationals) the exact cascade at threshold 1/7 from u = 1 fixes, at every move m and every reading k, the integer N and the side (blocked / clear) and the setter; each is a LINEAR inequality in rho (clear the denominator rho_setter > 0).
The cell = all rho satisfying the same inequalities with the same integers (strict).  The supremum of rho_min over the closure is a linear programme; floats (scipy) steer to an active set, the vertex is then solved EXACTLY with Fractions and checked
against every inequality exactly.  [PROVISIONAL: covering; supports: the description of the cell of one failing move type and the exact edge of rho_min on it, not an existence claim]  [OBS, F17: one type, from the witness r = 71/10]."""
import re, sys
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
src = open('modgap_real_adv_v5.out').read()
blocks = dict(re.findall(r"r = (\d\.\d): EXACT counterexample.*\n\s+rho = \[(.*?)\]", src))
def constraints(rho):
    """list of (coeffs a[0..5], b) meaning a.rho <= b (closed), derived from the exact cascade of the witness; plus the strictness is ignored (closure)."""
    cons = []; u = F(1); moves = []
    n = len(rho)
    def lin(kind, k, i, j, N, side):
        pass
    # state: u = (7*J + 1)/rho_i  (or 1 at the start); express x_k = rho_k*u/7 - N as linear form in rho after multiplying by rho_i (or by 1 at start)
    ui = None  # (J, i) or None for u = 1
    step = 0
    while True:
        bl = []
        for k, q in enumerate(rho):
            x = q * u / 7; N = round(x)
            blocked = abs(x - N) < F(1, 7)
            # |x - N| < 1/7  <=>  -1/7 < x - N < 1/7 ; with u = (7J+1)/rho_i : x - N = rho_k (7J+1)/(7 rho_i) - N
            def form(sign, off):
                # returns coefficient vector c and rhs so that  c.rho <= rhs  encodes   sign*(x - N) <= off   (closed)
                c = [F(0)] * 6
                if ui is None:   # u = 1, x - N = rho_k/7 - N
                    c[k] += F(sign, 7); return c, F(off) + sign * N
                J, i = ui
                c[k] += F(sign * (7 * J + 1), 7); c[i] -= F(sign * N) + F(off) * 0 + F(0)
                c[i] += -F(off)   # move off*rho_i to the left: sign*x - sign*N - off*rho_i... handled below
                return c, F(0)
            # write explicitly instead of the helper above
            if ui is None:
                if blocked:
                    cons.append(([F(1, 7) if t == k else F(0) for t in range(6)], F(1, 7) + N))      #  x - N <= 1/7
                    cons.append(([-F(1, 7) if t == k else F(0) for t in range(6)], F(1, 7) - N))     # -(x - N) <= 1/7
                else:
                    # clear: |x - N| >= 1/7 with N the nearest integer; side +: x - N >= 1/7, side -: x - N <= -1/7
                    if x - N >= 0: cons.append(([-F(1, 7) if t == k else F(0) for t in range(6)], -F(1, 7) - N))
                    else:          cons.append(([F(1, 7) if t == k else F(0) for t in range(6)], -F(1, 7) + N))
            else:
                J, i = ui
                def vec(ck, ci): 
                    c = [F(0)] * 6; c[k] += ck; c[i] += ci; return c
                a = F(7 * J + 1, 7)     # x - N = (a*rho_k - N*rho_i)/rho_i
                if blocked:
                    cons.append((vec(a, -F(N) - F(1, 7)), F(0)))         # a rho_k - N rho_i - rho_i/7 <= 0
                    cons.append((vec(-a, F(N) - F(1, 7)), F(0)))         # -(a rho_k - N rho_i) - rho_i/7 <= 0
                else:
                    if x - N >= 0: cons.append((vec(-a, F(N) + F(1, 7)), F(0)))     # a rho_k - N rho_i >= rho_i/7
                    else:          cons.append((vec(a, -F(N) + F(1, 7)), F(0)))      # a rho_k - N rho_i <= -rho_i/7
            if blocked: bl.append((F(7 * N + 1) / q, k, N))
        if not bl: return cons, u, False
        e, i, J = max(bl)
        # the setter i has the largest exit: (7 J_i + 1)/rho_i >= (7 J_k + 1)/rho_k for the other blockers k
        for e2, k, J2 in bl:
            if k != i:
                c = [F(0)] * 6; c[k] += F(7 * J + 1); c[i] -= F(7 * J2 + 1)    # (7J+1) rho_k >= (7J2+1) rho_i
                cons.append(([-x for x in c], F(0)))
        ui = (J, i); u = e; step += 1
        if u > 6:
            c = [F(0)] * 6; c[i] = F(-6); cons.append((c, -F(7 * J + 1)))        # (7J+1)/rho_i >= 6  <=>  6 rho_i <= 7J+1 ; written as 6 rho_i - (7J+1) <= 0
            cons[-1] = ([F(6) if t == i else F(0) for t in range(6)], F(7 * J + 1))
            return cons, u, True
def solve(rho, tag):
    cons, u, fail = constraints(rho)
    for c, b in cons:
        assert sum(ci * x for ci, x in zip(c, rho)) <= b, ("witness violates its own cell", c, b)
    A = [[float(x) for x in c] + [0.0] for c, b in cons]; B = [float(b) for c, b in cons]
    # variables rho_0..rho_5, z ; maximise z with z <= rho_k
    for k in range(6):
        row = [0.0] * 7; row[6] = 1.0; row[k] = -1.0; A.append(row); B.append(0.0)
    res = linprog([0] * 6 + [-1], A_ub=np.array(A), b_ub=np.array(B), bounds=[(0, None)] * 7, method='highs')
    print(tag, 'LP float optimum z =', res.x[6] if res.success else None, 'constraints', len(cons))
    return cons, res
if __name__ == '__main__':
    for r in ['7.1', '7.0', '6.5']:
        rho = [F(x.strip().strip("'")) for x in blocks[r].split(',')]
        rho = sorted(rho)
        solve(rho, 'witness r=' + r)
