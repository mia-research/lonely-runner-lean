# b12 library: exact cell constraints (homogeneous linear in the readings) of the path of an arrangement; exact vertex/dual checks.
# Everything stated as fact is Fraction arithmetic.  scipy floats only steer (choose a basis); the basis is then verified exactly.
import sys
from fractions import Fraction as F
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
import numpy as np
from scipy.optimize import linprog

def norm(rhos):
    rhos = sorted(rhos); m = rhos[0]; return [r / m for r in rhos]

def cell_rows(rhos):
    """rhos: exact, rho_1 = 1 after norm.  Returns (rows, tags, final) ; each row (a[0..6]) means sum a_i rho_{i+1} >= 0 (closure of the cell).
    tags describe the framework meaning."""
    rhos = norm(rhos); n = 7
    steps, Rend = path(rhos)
    rows = []; tags = []
    def add(a, tag):
        if any(a): rows.append(a); tags.append(tag)
    # states: k=0: R=1/rho_1 (c=1, s=0); k>=1: c=8*lap+1, s=setter of move k
    states = [(1, 0)] + [(8 * st['lap'] + 1, st['setter']) for st in steps]
    for k, (c, s) in enumerate(states):
        R = F(c) / rhos[s]
        blk = [y for y in range(n) if blocks(R, rhos[y])]
        for y in range(n):
            u = R * rhos[y]
            if y in blk:
                j = round(u / 8)
                a = [0] * n; a[y] += c; a[s] -= (8 * j - 1); add(a, ('state %d: R=%s/rho%d; rho%d blocked, lap %d: its entry (8j-1)/rho%d <= R' % (k, c, s + 1, y + 1, j, y + 1), 'entry', k, y + 1, j))
                a = [0] * n; a[s] += (8 * j + 1); a[y] -= c; add(a, ('exit', 'R <= exit', k, y + 1, j))
            else:
                j = int(u // 8)
                a = [0] * n; a[y] += c; a[s] -= (8 * j + 1); add(a, ('clear-low', 'exit of (y,j) <= R', k, y + 1, j))
                a = [0] * n; a[s] += (8 * j + 7); a[y] -= c; add(a, ('clear-high', 'R <= entry of (y,j+1)', k, y + 1, j + 1))
        if k < len(steps):
            st = steps[k]; sj = st['lap']; S = st['setter']
            for y in st['blockers']:
                if y == S: continue
                jy = round(R * rhos[y] / 8)
                a = [0] * n; a[y] += (8 * sj + 1); a[S] -= (8 * jy + 1)   # exit_S >= exit_y: (8sj+1)/rho_S >= (8jy+1)/rho_y  -> (8sj+1) rho_y >= (8jy+1) rho_S
                add(a, ('setter', 'exit(S,lap) >= exit(y,j)', k, y + 1, jy, S + 1, sj))
    for i in range(n - 1):
        a = [0] * n; a[i + 1] = 1; a[i] = -1; add(a, ('order', i + 2))
    return rows, tags, (steps, Rend)

def row_val(a, x):  # x = exact list of 7 readings
    return sum(F(ai) * xi for ai, xi in zip(a, x))

def feasible_exact(rows, x):
    return all(row_val(a, x) >= 0 for a in rows)

def solve_exact(A, b):
    """Exact Gaussian elimination; A list of rows (Fractions), b list.  Returns unique solution list or None (singular/inconsistent)."""
    m = len(A); n = len(A[0]); M = [list(map(F, A[i])) + [F(b[i])] for i in range(m)]
    r = 0; piv = []
    for c in range(n):
        p = next((i for i in range(r, m) if M[i][c] != 0), None)
        if p is None: return None
        M[r], M[p] = M[p], M[r]; pv = M[r][c]; M[r] = [v / pv for v in M[r]]
        for i in range(m):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [vi - f * vr for vi, vr in zip(M[i], M[r])]
        piv.append(c); r += 1
    for i in range(r, m):
        if M[i][n] != 0: return None
    return [M[i][n] for i in range(n)]

def min_rho_s_exact(rows, s_idx, hint=None, cvec=None):
    """Minimise rho_{s_idx+1} over the closed cell (rho_1 = 1).  Float LP chooses a basis; returned value is exact with an exact primal
    feasibility check and an exact dual (Farkas) certificate; else None."""
    n = 7
    # variables x = rho_2..rho_7 ; row: a0*1 + sum a_i x_i >= 0
    A = np.array([[float(v) for v in a[1:]] for a in rows]); b = np.array([float(a[0]) for a in rows])
    c = np.zeros(6)
    if cvec is None: c[s_idx - 2] = 1.0
    else: c = np.array([float(t) for t in cvec])
    res = linprog(c, A_ub=-A, b_ub=b, bounds=[(None, None)] * 6, method='highs')
    if res.status != 0: return None
    duals = -res.ineqlin.marginals  # >=0 for active rows
    basis = [i for i in range(len(rows)) if duals[i] > 1e-12]
    cand = basis
    def attempt(idx):
        Ar = [[F(v) for v in rows[i][1:]] for i in idx]; br = [-F(rows[i][0]) for i in idx]
        if len(idx) != 6: return None
        x = solve_exact(Ar, br)
        if x is None: return None
        X = [F(1)] + x
        if not feasible_exact(rows, X): return None
        # dual: sum lam_i a_i[1:] = c ; lam >= 0
        At = [[F(rows[i][1:][r]) for i in idx] for r in range(6)]
        cc = [F(1) if r == s_idx - 2 else F(0) for r in range(6)] if cvec is None else [F(t) for t in cvec]
        lam = solve_exact(At, cc)
        if lam is None or any(l < 0 for l in lam): return None
        return X, dict(zip(idx, lam))
    if len(cand) == 6:
        r = attempt(cand)
        if r: return r
    # degenerate: add float-active rows and try subsets of size 6 containing the dual-positive rows
    act = [i for i in range(len(rows)) if abs(float(rows[i][0]) + float(np.dot(rows[i][1:], res.x))) < 1e-7 * max(1.0, abs(float(rows[i][0])))]
    from itertools import combinations
    rest = [i for i in act if i not in cand]
    need = 6 - len(cand)
    if need < 0 or len(rest) > 24: return None
    for comb in combinations(rest, need):
        r = attempt(cand + list(comb))
        if r: return r
    return None

def sigkey(tags, steps):
    out = []
    for t in tags:
        kind = t[0] if t[0] in ('exit', 'clear-low', 'clear-high', 'setter', 'order') else 'entry'
        out.append((kind,) + tuple(x for x in t[1:] if not isinstance(x, str)))
    return tuple(out)

def gate_ok(steps, minlen=20):
    return any(s['setter'] == 0 for s in steps) and len(steps) >= minlen

def cell_info(x, with_sup=True):
    """x exact (rho_1 normalised).  Returns dict: rows,tags,steps,R,sig, sup (exact, closure) with its optimal vertex and dual, or None."""
    x = norm(x)
    rows, tags, (steps, R) = cell_rows(x)
    d = dict(x=x, rows=rows, tags=tags, steps=steps, R=R, sig=sigkey(tags, steps), n=len(steps))
    if steps and with_sup:
        last = steps[-1]; s = last['setter'] + 1; c = 8 * last['lap'] + 1
        r = min_rho_s_exact(rows, s)
        d['sup'] = None
        if r:
            X, lam = r; d['X'] = X; d['lam'] = lam; d['sup'] = F(c) / X[s - 1]
    return d

def row_meaning(tag):
    k = tag[0]
    if k == 'order': return 'order: rho%d <= rho%d' % (tag[1] - 1, tag[1])
    if k == 'exit': return 'state %d: R <= exit(rho%d lap %d)' % (tag[2], tag[3], tag[4])
    if k == 'clear-low': return 'state %d: exit(rho%d lap %d) <= R (clear after zone)' % (tag[2], tag[3], tag[4])
    if k == 'clear-high': return 'state %d: R <= entry(rho%d lap %d) (clear before zone)' % (tag[2], tag[3], tag[4])
    if k == 'setter': return 'move %d: exit(rho%d lap %d) >= exit(rho%d lap %d) (setter largest)' % (tag[2], tag[5], tag[6], tag[3], tag[4])
    return 'state %d: entry(rho%d lap %d) <= R (blocked)' % (tag[2], tag[3], tag[4])
