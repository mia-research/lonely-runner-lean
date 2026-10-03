# sigpair_lib_v1 -- exhaustive decision of (opener rank, closer rank) pairs per tree cell (window rho_7 <= 8J+1).
# Region searched per cell = {rho: rho_1=1<rho_2<..<rho_7<=W, rho in box(+-EPS), exact cascade follows the cell's `path` and lands, closer = reading c}.
# Rows are linear in rho; every strict row carries slack t (row scaled to unit L2 norm in rho), LP maximises t (t in [-1,1]); HiGHS warm-started stack
# (rows pushed/popped along the DFS).  Path conditions (exact characterisation of "the cascade follows the path"):
#   state k (R_k=(8 j_k+1)/rho_{s_k}, s_0=0, j_0=0): setter s_{k+1} is blocked in lap j_{k+1}; every other reading y != s_k, s_{k+1} is either clear
#   (gap G(l) = u in [8l+1, 8l+7]) or blocked in lap l (u in [8l-1, 8l+1]) with exit (8l+1)/rho_y <= R_{k+1}; y = s_k sits at its own exit (clear).
#   final state m: every reading clear, in a gap G(l_y); closer = argmin_y (8 l_y+7)/rho_y (ties to the lower rank).
import numpy as np, math
from fractions import Fraction as F
from scipy.optimize._highspy import _core

EPS = 1e-9        # box relaxation (superset: only enlarges the region searched)
KS = 1000.0       # internal scale: x' = KS*x, t' = KS*t (HiGHS absolute tolerance 1e-10 then acts as 1e-13 on x, t)
TOL = 1e-11       # |t| <= TOL : inconclusive / degenerate (t in rho units, rows unit-normalised)
INF = _core.kHighsInf

class Cell:
    def __init__(self, path, box, J):
        self.path = [(int(r) - 1, int(l)) for r, l in path]
        self.m = len(path)
        self.lo = [float(b[0]) for b in box]; self.hi = [float(b[1]) for b in box]
        self.W = 8 * J + 1
        self.s = [0] + [r for r, l in self.path]
        self.j = [0] + [l for r, l in self.path]

class Stack:
    def __init__(self, cell):
        self.cell = cell; self.n = 0; self.tags = []; self.nlp = 0; self.ex = []; self.exr = []
        h = _core._Highs(); self.h = h
        h.setOptionValue('output_flag', False)
        h.setOptionValue('primal_feasibility_tolerance', 1e-10); h.setOptionValue('dual_feasibility_tolerance', 1e-10)
        e = np.array([], dtype=np.int32); ev = np.array([])
        for j in range(8):
            if j == 0: lo, hi, cost = KS, KS, 0.0
            elif j == 7: lo, hi, cost = -KS, KS, -1.0
            else: lo, hi, cost = KS * max(1.0, cell.lo[j] - EPS), KS * min(float(cell.W), cell.hi[j] + EPS), 0.0
            h.addCol(cost, lo, hi, 0, e, ev)
        for i in range(6): self.add({i: 1, i + 1: -1}, 0, True, 'ord')
        self.add({6: 1}, cell.W, False)
    def add(self, d, b, strict=True, tag=''):
        nm = math.sqrt(sum(v * v for v in d.values()))
        idx = list(d.keys()); val = [v / nm for v in d.values()]
        if strict: idx.append(7); val.append(1.0)
        self.h.addRow(-INF, KS * float(b) / nm, len(idx), np.array(idx, dtype=np.int32), np.array(val, dtype=float))
        self.n += 1; self.tags.append(tag); self.ex.append((dict(d), F(b), strict, F(nm).limit_denominator(10**6)))
        co = [F(0)] * 6; rhs = F(b)
        for i, v in d.items():
            if i == 0: rhs -= v
            else: co[i - 1] += v
        self.exr.append((co, rhs, strict))
    def mark(self): return self.n
    def rollback(self, mk):
        if self.n > mk:
            self.h.deleteRows(self.n - mk, np.arange(mk, self.n, dtype=np.int32)); self.n = mk; del self.tags[mk:]; del self.ex[mk:]; del self.exr[mk:]
    def solve(self):
        self.nlp += 1
        self.h.run()
        st = self.h.getModelStatus()
        if st != _core.HighsModelStatus.kOptimal: return None
        x = np.array(self.h.getSolution().col_value)
        return float(x[7]) / KS, x[:7] / KS
    def solve_full_slack(self):
        """slack on every row (nonstrict rows too): interior point of the closed system, or None"""
        qs = [q for q in range(self.n) if not self.ex[q][2]]
        for q in qs: self.h.changeCoeff(q, 7, 1.0)
        r = self.solve()
        for q in qs: self.h.changeCoeff(q, 7, 0.0)
        return r
    def solve_ignore_order(self):
        # order rows are the first 6 rows (strict, normalised by sqrt(2)): zero their t coefficient, solve, restore
        for q in range(6): self.h.changeCoeff(q, 7, 0.0)
        r = self.solve()
        for q in range(6): self.h.changeCoeff(q, 7, 1.0)
        return r

def _gauss(eqs, n=7):
    """eqs: list of (coef list len n, rhs) Fractions; returns solution if rank n else None (first n independent equations used, others must be consistent)"""
    M = [list(e[0]) + [e[1]] for e in eqs]; piv = []; r = 0
    for col in range(n):
        p = None
        for i in range(r, len(M)):
            if M[i][col] != 0: p = i; break
        if p is None: return None
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][col]; M[r] = [v * inv for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][col] != 0:
                f = M[i][col]; M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    for i in range(r, len(M)):
        if M[i][n] != 0: return None
    return [M[i][n] for i in range(n)]

def polish(S):
    """exact vertex of the current LP's optimal basis (unknowns x1..x6, t); returns exact rho list (rho_1=1) satisfying every stored row exactly (strict rows strictly), else None"""
    h = S.h; b = h.getBasis()
    if not b.valid: return None
    B = _core.HighsBasisStatus.kBasic
    eqs = []
    for q, st in enumerate(b.row_status):
        if st == B: continue
        d, rhs, strict, nm = S.ex[q]
        co = [F(0)] * 7
        for i, v in d.items():
            if i == 0: rhs = rhs - v
            else: co[i - 1] += v
        co[6] = nm if strict else F(0)
        eqs.append((co, rhs))
    cell = S.cell
    for j in range(1, 8):
        st = b.col_status[j]
        if st == B: continue
        if j < 7:
            lo, hi = max(1.0, cell.lo[j] - EPS), min(float(cell.W), cell.hi[j] + EPS)
            val = F(lo) if st == _core.HighsBasisStatus.kLower else F(hi)
        else: val = F(1) if st == _core.HighsBasisStatus.kUpper else F(-1)
        co = [F(0)] * 7; co[j - 1] = F(1); eqs.append((co, val))
    sol = _gauss(eqs)
    if sol is None: return None
    rho = [F(1)] + sol[:6]
    for (d, rhs, strict, nm) in S.ex:
        v = sum(c * rho[i] for i, c in d.items())
        if (v >= rhs) if strict else (v > rhs): return None
    return rho

def interior_exact(S):
    """relative-interior exact point of the current closed/strict system: (1) full-slack solve; (2) if that fails (t<=TOL), find nonstrict rows that are implicit
    equalities (max slack <= 1e-9 while strict rows keep slack >= 1e-9), pin them, full-slack on the rest, project the float point exactly onto the pinned
    equalities (rational least-squares).  Returns exact rho list satisfying every stored row exactly, or None."""
    r = S.solve_full_slack()
    if r is not None and r[0] > TOL:
        return [F(1)] + [F(float(v)).limit_denominator(10**12) for v in r[1][1:]], ('full', r[0])
    h = S.h; nr = S.n
    strict_rows = [q for q in range(nr) if S.ex[q][2]]
    nons = [q for q in range(nr) if not S.ex[q][2]]
    # 1. implicit equalities
    h.changeColBounds(7, 1e-9 * KS, KS)
    cost_save = [0.0] * 7 + [-1.0]
    eqrows = []
    for q in nons:
        d, rhs, strict, nm = S.ex[q]
        a = [0.0] * 8
        for i, v in d.items(): a[i] += float(v)
        nmf = math.sqrt(sum(float(v) ** 2 for v in d.values()))
        for j in range(8): h.changeColCost(j, a[j] / nmf)       # minimise a.x  (maximise slack b-a.x)
        h.run()
        if h.getModelStatus() != _core.HighsModelStatus.kOptimal:
            for j in range(8): h.changeColCost(j, cost_save[j])
            h.changeColBounds(7, -KS, KS); return None, ('region empty at slack 1e-9', 0)
        x = np.array(h.getSolution().col_value) / KS
        if (float(rhs) / nmf) - sum(a[j] * x[j] for j in range(7)) / nmf <= 1e-9: eqrows.append(q)
    for j in range(8): h.changeColCost(j, cost_save[j])
    h.changeColBounds(7, -KS, KS)
    # 2. pin them, full slack on the rest
    for q in eqrows:
        d, rhs, strict, nm = S.ex[q]; nmf = math.sqrt(sum(float(v) ** 2 for v in d.values()))
        h.changeRowBounds(q, KS * float(rhs) / nmf, KS * float(rhs) / nmf)
    rest = [q for q in nons if q not in eqrows]
    for q in rest: h.changeCoeff(q, 7, 1.0)
    r = S.solve()
    for q in rest: h.changeCoeff(q, 7, 0.0)
    for q in eqrows:
        d, rhs, strict, nm = S.ex[q]; nmf = math.sqrt(sum(float(v) ** 2 for v in d.values()))
        h.changeRowBounds(q, -INF, KS * float(rhs) / nmf)
    if r is None or r[0] <= TOL: return None, ('no interior after pinning', None if r is None else r[0])
    xf = [F(1)] + [F(float(v)) for v in r[1][1:]]
    # 3. exact projection onto pinned equalities: x = xf + E^T (E E^T)^-1 (e - E xf)   (x0 = 1 fixed: work on coordinates 1..6)
    E = []; e = []
    for q in eqrows:
        d, rhs, strict, nm = S.ex[q]; co = [F(0)] * 6; rr = F(rhs)
        for i, v in d.items():
            if i == 0: rr -= v
            else: co[i - 1] += v
        E.append(co); e.append(rr)
    if E:
        resid = [e[k] - sum(E[k][i] * xf[i + 1] for i in range(6)) for k in range(len(E))]
        # solve (E E^T) y = resid, with possible dependent rows -> gauss on independent subset
        G = [[sum(E[k][i] * E[l][i] for i in range(6)) for l in range(len(E))] + [resid[k]] for k in range(len(E))]
        # gaussian elimination with rank detection
        n = len(E); M = G; piv = []; rr_ = 0
        for col in range(n):
            p = None
            for i in range(rr_, n):
                if M[i][col] != 0: p = i; break
            if p is None: continue
            M[rr_], M[p] = M[p], M[rr_]; inv = 1 / M[rr_][col]; M[rr_] = [v * inv for v in M[rr_]]
            for i in range(n):
                if i != rr_ and M[i][col] != 0:
                    f = M[i][col]; M[i] = [a - f * b for a, b in zip(M[i], M[rr_])]
            piv.append(col); rr_ += 1
        yv = [F(0)] * n
        for k, col in enumerate(piv): yv[col] = M[k][n]
        for i in range(6): xf[i + 1] += sum(E[k][i] * yv[k] for k in range(n))
    for (d, rhs, strict, nm) in S.ex:
        v = sum(c * xf[i] for i, c in d.items())
        if (v >= rhs) if strict else (v > rhs): return None, ('projection violates exact rows', None)
    return xf, ('pinned', len(eqrows))

def u_interval(cell, k, y):
    s = cell.s[k]; c = 8 * cell.j[k] + 1
    return c * (cell.lo[y] - EPS) / (cell.hi[s] + EPS), c * (cell.hi[y] + EPS) / max(cell.lo[s] - EPS, 1.0)

def add_G(S, k, y, l):
    c = S.cell; s = c.s[k]; cc = 8 * c.j[k] + 1
    S.add({s: 8 * l + 1, y: -cc}, 0, False)      # clear = closed gap [8l+1, 8l+7]
    S.add({y: cc, s: -(8 * l + 7)}, 0, False)

def add_B(S, k, y, l):
    c = S.cell; s = c.s[k]; cc = 8 * c.j[k] + 1
    S.add({s: 8 * l - 1, y: -cc}, 0, True)
    S.add({y: cc, s: -(8 * l + 1)}, 0, True)
    s1 = c.s[k + 1]; c1 = 8 * c.j[k + 1] + 1
    S.add({s1: 8 * l + 1, y: -c1}, 0, y > s1)       # exit_y <= exit_setter; strict against higher index (outcome() breaks exit ties to the larger index)

def options(cell, k, y, final):
    umin, umax = u_interval(cell, k, y); out = []
    for l in range(0, int(umax // 8) + 3):
        if 8 * l + 7 >= umin and 8 * l + 1 <= umax: out.append(('G', l))
        if not final and l >= 1 and 8 * l + 1 >= umin and 8 * l - 1 <= umax: out.append(('B', l))
    return out

def add_closer(S, laps, c, tie_ok=True):
    """closer = reading c.  tie_ok=False: all rows strict.  tie_ok=True: rows against higher-rank y nonstrict (ties go to the lower rank)."""
    for y in range(7):
        if y == c: continue
        S.add({y: 8 * laps[c] + 7, c: -(8 * laps[y] + 7)}, 0, not (tie_ok and y > c))

def decisions(cell):
    """(final-state decisions, intermediate decisions)"""
    m = cell.m; fin = [(m, y, True) for y in range(7) if y != cell.s[m]]; inter = []
    for k in range(m):
        for y in range(7):
            if y == cell.s[k] or y == cell.s[k + 1]: continue
            inter.append((k, y, False))
    return fin, inter

def setup(cell):
    S = Stack(cell); c = cell
    for k in range(c.m):
        s = c.s[k + 1]; p = c.s[k]; cc = 8 * c.j[k] + 1; l = c.j[k + 1]
        S.add({p: 8 * l - 1, s: -cc}, 0, True)
        S.add({s: cc, p: -(8 * l + 1)}, 0, True)
    return S

def dfs(cell, S, dec, laps, on_leaf, node_budget=20000):
    """enumerate decision combinations of `dec` with LP pruning (t >= -TOL); on_leaf(laps, t, x) at every leaf, True return stops the search.
    returns (leaves, nodes, over_budget, stopped)"""
    cnt = {'leaves': 0, 'nodes': 0, 'over': False}
    def rec(i):
        if cnt['nodes'] > node_budget: cnt['over'] = True; return False
        if i == len(dec):
            r = S.solve()
            if r is None or r[0] < -TOL: return False
            cnt['leaves'] += 1
            return bool(on_leaf(laps, r[0], r[1]))
        k, y, final = dec[i]
        for (t, l) in options(cell, k, y, final):
            mk = S.mark()
            (add_G if t == 'G' else add_B)(S, k, y, l)
            cnt['nodes'] += 1
            r = S.solve()
            if r is not None and r[0] >= -TOL:
                if final: laps[y] = l
                stop = rec(i + 1)
                if final: del laps[y]
                if stop: S.rollback(mk); return True
            S.rollback(mk)
        return False
    stopped = rec(0)
    return cnt['leaves'], cnt['nodes'], cnt['over'], stopped
