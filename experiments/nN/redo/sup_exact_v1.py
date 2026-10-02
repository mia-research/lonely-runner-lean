# Exact value of the supremum of the landing in the window rho_7 <= 9: follow the path of the maximising node through the tree, take the LP optimum
# (minimum of the definer's reading over the closure of the cell), recover the vertex exactly from the active constraints (sympy rational solve).
import sys, ast
sys.argv = [sys.argv[0], "1"]
src = open('path_tree_par.py').read().split('if __name__ == "__main__":')[0]
exec(src)
import sympy as sp
PATH = [(7, 1), (6, 1), (5, 1), (4, 1), (7, 2), (3, 1), (6, 2), (5, 2), (2, 1), (4, 2), (6, 3), (7, 4), (5, 3), (3, 2), (6, 4), (4, 3), (5, 4), (7, 6), (2, 2), (1, 1), (5, 6), (4, 5), (2, 3), (5, 7), (6, 8), (4, 6), (7, 11)]
def children(cons, x, J):
    out = []
    ranges = {y: rho_range(cons, y) for y in range(7)}
    for w in range(7):
        if w == x: continue
        umin, umax = u_range(ranges, x, J, w)
        for j in range(max(1, int((umin - 1) // 8)), int((umax + 1) // 8) + 2):
            chain = [Con(vec([(w, 8 * J + 1), (x, -(8 * j - 1))]), True), Con(vec([(x, 8 * j + 1), (w, -(8 * J + 1))]), True)]
            ok, _ = feasible(cons + chain)
            if not ok: continue
            base = cons + chain; pend = []
            ranges2 = {y: rho_range(base, y) for y in range(7)}
            for y in range(7):
                if y == w or y == x: continue
                umin_y, umax_y = u_range(ranges2, x, J, y)
                for jp in range(max(1, int((umin_y - 1) // 8)), int((umax_y + 1) // 8) + 2):
                    s1 = Con(vec([(y, 8 * J + 1), (x, -(8 * jp - 1))]), True); s2 = Con(vec([(w, 8 * jp + 1), (y, -(8 * j + 1))]), y < w)
                    ok2, _ = feasible(base + [s1, s2])
                    if ok2: pend.append((y, jp, s1, s2))
            def rec(i, cur):
                if i == len(pend):
                    ok3, _ = feasible(cur)
                    if ok3: out.append((w, j, cur))
                    return
                y, jp, s1, s2 = pend[i]
                A = Con(vec([(x, 8 * jp - 1), (y, -(8 * J + 1))]), False)
                okA, _ = feasible(cur + [A])
                if okA: rec(i + 1, cur + [A])
                negs2 = Con(vec([(y, 8 * j + 1), (w, -(8 * jp + 1))]), y > w)
                okB, _ = feasible(cur + [s1, negs2])
                if okB: rec(i + 1, cur + [s1, negs2])
            rec(0, base)
    return out
cells = [(root(), 0, 0)]
for depth, (w1, j) in enumerate(PATH):
    nxt = []
    for cons, x, J in cells:
        for w, jj, cc in children(cons, x, J):
            if (w + 1, jj) == (w1, j): nxt.append((cc, w, jj))
    cells = nxt
    print("depth %d: %d cells following the path" % (depth + 1, len(cells)), flush=True)
best = None
for cons, x, J in cells:
    # minimise rho_x over the closure of the cell
    A = [list(-k.c) for k in cons]; b = [k.c0 for k in cons]
    cobj = [0.0] * NV
    if x == 0: continue
    cobj[x - 1] = 1.0
    res = linprog(cobj, A_ub=np.array(A), b_ub=np.array(b), bounds=[(0, RHOMAX + 1)] * NV, method="highs")
    R = (8 * J + 1) / res.x[x - 1]
    if best is None or R > best[0]: best = (R, res.x, cons, x, J)
R, v, cons, x, J = best
print("sup R = %.12f at the definer rho_%d = %.12f (lap %d)" % (R, x + 1, v[x - 1], J))
# exact vertex from the active constraints
act = []
for k in cons:
    sl = float(k.ec0) + sum(float(c) * xx for c, xx in zip(k.ec, v))
    if abs(sl) < 1e-7: act.append(k)
print("active constraints:", len(act))
syms = sp.symbols("r2:8"); eqs = []
for k in act: eqs.append(sp.Eq(sp.Rational(k.ec0.numerator, k.ec0.denominator) + sum(sp.Rational(c.numerator, c.denominator) * s for c, s in zip(k.ec, syms)), 0))
sol = sp.solve(eqs, syms, dict=True)
print("exact vertex:", sol)
if sol:
    sv = sol[0]
    rho = [sp.Integer(1)] + [sv.get(s, None) for s in syms]
    print("readings:", rho, [float(r) if r is not None else None for r in rho])
    if all(r is not None for r in rho):
        rx = rho[x]; print("exact sup R = (8*%d+1)/rho_%d = %s = %.12f" % (J, x + 1, sp.nsimplify(sp.Integer(8 * J + 1) / rx), float(sp.Integer(8 * J + 1) / rx)))
