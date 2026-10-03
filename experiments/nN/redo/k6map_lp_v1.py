# k6map LP library (v1): exact fine cell of the K6 structure of six readings, and the exact LP for min  rho_6 * L_max  over the closed cell.
# Variables u_y = 1/rho_y (zone endpoints (8j-1)u_y, (8j+1)u_y are LINEAR in u).  Cell = sorted order of all zone endpoints in the window and the bounds lo = u_1, hi = 7 u_1.
# Objective rho_6 * L_i = L_i(u)/u_6 : linear-fractional -> Charnes-Cooper (w = u/u_6): LP in w_1..w_5, t with w_6 = 1.  Floats (scipy) choose a basis only;
# the vertex is an exact Fraction solve, checked against EVERY row in Fractions, and the optimality is certified by an exact dual (multipliers >= 0).
import sys, itertools, random
sys.path.insert(0, '.')
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
from k6map_lib_v1 import K6
N = 6
def events(rho):
    """list of (value, kind, y, j, coef) for the base point; kind 'in'/'out'; plus bounds. Complete in the sense described in the header."""
    hi = 7 * (1 / rho[0]); ev = []
    for y in range(1, N):            # reading 1's own zones start at 7 = hi (open zone): none inside [1,7]
        u = 1 / rho[y]; j = 1
        while True:
            e_in = (8 * j - 1) * u
            ev.append((e_in, 'in', y, j, 8 * j - 1)); ev.append(((8 * j + 1) * u, 'out', y, j, 8 * j + 1))
            if e_in > hi: break
            j += 1
    ev.append((1 / rho[0], 'lo', 0, 0, 1)); ev.append((hi, 'hi', 0, 0, 7))
    return ev
def signature(rho):
    ev = sorted(events(rho)); keys = [(k, y, j) for v, k, y, j, c in ev]
    vals = [v for v, *_ in ev]
    if len(set(vals)) < len(vals): return None, None
    return tuple(keys), ev
def cell(rho):
    """rows (list of coefficient vectors c over u_1..u_6, meaning c.u >= 0) and components [(start_form, end_form)] ; None if the base point is not generic."""
    sig, ev = signature(rho)
    if sig is None: return None
    def form(e):
        v = [F(0)] * N
        if e[1] in ('lo', 'hi'): v[0] = F(e[4])
        else: v[e[2]] = F(e[4])
        return v
    rows = []
    for e1, e2 in zip(ev, ev[1:]):
        f1, f2 = form(e1), form(e2); rows.append([b - a for a, b in zip(f1, f2)])
    for i in range(N - 1):               # u_i >= u_{i+1}  (rho increasing); u_6 >= 0
        v = [F(0)] * N; v[i] = F(1); v[i + 1] = F(-1); rows.append(v)
    v = [F(0)] * N; v[N - 1] = F(1); rows.append(v)
    # components by a depth scan
    pos_lo = next(i for i, e in enumerate(ev) if e[1] == 'lo'); pos_hi = next(i for i, e in enumerate(ev) if e[1] == 'hi')
    depth = sum(1 for e in ev[:pos_lo] if e[1] == 'in') - sum(1 for e in ev[:pos_lo] if e[1] == 'out')
    comps = []; start = ev[pos_lo] if depth == 0 else None
    for e in ev[pos_lo + 1:pos_hi]:
        if e[1] == 'in':
            if depth == 0: comps.append((start, e))
            depth += 1
        elif e[1] == 'out':
            depth -= 1
            if depth == 0: start = e
    if depth == 0: comps.append((start, ev[pos_hi]))
    cf = []
    for s, e in comps:
        fs, fe = form(s), form(e); cf.append([b - a for a, b in zip(fs, fe)])
    return sig, rows, comps, cf
def exact_lp(rows, cf):
    """min t s.t. rows.u >= 0 (u = w), w_6 = 1, cf_i.w <= t.  Unknowns x = (w_1..w_5, t).  Returns (value, w (6 Fractions), certificate ok) or None."""
    m = len(rows); nv = 6
    Ar = []; br = []     # constraints g.x >= h
    for r in rows: Ar.append([r[i] for i in range(5)] + [F(0)]); br.append(-r[5])          # r.w >= 0 with w_6 = 1
    for c in cf: Ar.append([-c[i] for i in range(5)] + [F(1)]); br.append(c[5])           # t - c.w >= 0 -> t >= c.w ; c.w = c[:5].w + c[5]
    A = np.array([[float(v) for v in a] for a in Ar]); b = np.array([float(v) for v in br])
    cvec = np.zeros(nv); cvec[5] = 1.0
    res = linprog(cvec, A_ub=-A, b_ub=-b, bounds=[(None, None)] * nv, method='highs')
    if res.status != 0: return None
    duals = -res.ineqlin.marginals
    cand = [i for i in range(len(Ar)) if duals[i] > 1e-12]
    def attempt(idx):
        if len(idx) != nv: return None
        x = solve_exact([[F(v) for v in Ar[i]] for i in idx], [F(br[i]) for i in idx])
        if x is None: return None
        for a, h in zip(Ar, br):
            if sum(F(p) * q for p, q in zip(a, x)) < h: return None
        At = [[F(Ar[i][r]) for i in idx] for r in range(nv)]
        cc = [F(0)] * 5 + [F(1)]
        lam = solve_exact(At, cc)
        if lam is None or any(l < 0 for l in lam): return None
        return x, lam, list(idx)
    r = attempt(cand) if len(cand) == nv else None
    if r is None:
        act = [i for i in range(len(Ar)) if abs(float(br[i]) - float(np.dot(A[i], res.x))) < 1e-7 * max(1.0, abs(float(br[i])))]
        rest = [i for i in act if i not in cand]; need = nv - len(cand)
        if need < 0 or len(rest) > 22: return None
        for comb in itertools.combinations(rest, need):
            r = attempt(cand + list(comb))
            if r: break
    if r is None: return None
    x, lam, idx = r
    return x[5], x[:5] + [F(1)], dict(zip(idx, lam))
def solve_exact(A, b):
    m = len(A); n = len(A[0]); M = [list(map(F, A[i])) + [F(b[i])] for i in range(m)]
    r = 0
    for c in range(n):
        p = next((i for i in range(r, m) if M[i][c] != 0), None)
        if p is None: return None
        M[r], M[p] = M[p], M[r]; pv = M[r][c]; M[r] = [v / pv for v in M[r]]
        for i in range(m):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [vi - f * vr for vi, vr in zip(M[i], M[r])]
        r += 1
    for i in range(r, m):
        if M[i][n] != 0: return None
    return [M[i][n] for i in range(n)]
def w_to_rho(w):
    return [w[0] / wi for wi in w]            # rho_i = u_1... rho_i = 1/u_i with u_1 = 1: rho_i = w_1 / w_i
def ratio_of(rho):
    W = K6(rho); L = max((b - a for a, b in W), default=F(-1))
    return L * 7 * rho[5] / 2, L
