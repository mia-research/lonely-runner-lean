# sigpair_exact_v1 -- EXACT decision of one (opener, closer) pair in a tree cell.
# Verdicts are statements about exact rationals:
#   FEAS : an exact Fraction arrangement, outcome() gives (opener rank, closer rank) = the target pair (path equal to the cell's path recorded too)
#   INF  : every node of the decision tree is either excluded by an EXACT Farkas certificate (multipliers lambda >= 0 in Fractions with
#          sum lambda_q a_q = 0 and sum lambda_q b_q < 0, or = 0 with positive multiplier mass on a strict row), or by exact interval arithmetic
#   UNCERT : some pruned node had no exact certificate and no exact witness (count reported)
# Floats (HiGHS) are used only to GUESS multipliers / points; every accepted object is re-verified in Fractions.
# Region = cell box (as stored, relaxed by exactly 1/10^9 each side, clipped to [1, W]) + rho_1 = 1 < rho_2 < ... < rho_7 <= W + cascade follows the cell path
# (setter blocked in lap, others clear in closed gaps or blocked in open zones with exit <= next state) + closer = target.
import sys, math, pickle, time
import numpy as np
from fractions import Fraction as F
sys.path.insert(0, '.')
from sigpair_lib_v1 import *
from sigpair_lib_v1 import _core, _gauss
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])

EPSF = F(1, 10**9)

def exact_bounds(cell):
    lo = [F(1)] + [max(F(1), F(cell.lo[j]) - EPSF) for j in range(1, 7)]
    hi = [F(1)] + [min(F(cell.W), F(cell.hi[j]) + EPSF) for j in range(1, 7)]
    return lo, hi

def exact_rows(S, lo, hi):
    """rows over x1..x6: (coef list(6), rhs, strict) : stack rows (cached exact form) then lower/upper bound rows"""
    br = getattr(S, '_br', None)
    if br is None:
        br = []
        for j in range(1, 7):
            co = [F(0)] * 6; co[j - 1] = F(-1); br.append((co, -lo[j], False))
            co = [F(0)] * 6; co[j - 1] = F(1); br.append((co, hi[j], False))
        S._br = br
    return S.exr + br

def _project(cols, A, n):
    """cols: guess vector (Fractions, len n); A: list of equations (list len n, rhs): returns guess projected exactly onto A lam = rhs (least-norm correction)"""
    m = len(A)
    G = [[sum(A[k][0][i] * A[l][0][i] for i in range(n)) for l in range(m)] + [A[k][1] - sum(A[k][0][i] * cols[i] for i in range(n))] for k in range(m)]
    M = G; piv = []; r = 0
    for col in range(m):
        p = None
        for i in range(r, m):
            if M[i][col] != 0: p = i; break
        if p is None: continue
        M[r], M[p] = M[p], M[r]; inv = 1 / M[r][col]; M[r] = [v * inv for v in M[r]]
        for i in range(m):
            if i != r and M[i][col] != 0:
                f = M[i][col]; M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(col); r += 1
    for i in range(r, m):
        if M[i][m] != 0: return None
    y = [F(0)] * m
    for k, col in enumerate(piv): y[col] = M[k][m]
    return [cols[i] + sum(A[k][0][i] * y[k] for k in range(m)) for i in range(n)]

def lp_duals(S, closed):
    """solve with slack on all rows (closed=True) or the strict-row LP; returns (t, row_dual list, col_dual list) with t bounds widened"""
    h = S.h; nons = [q for q in range(S.n) if not S.ex[q][2]]
    h.changeColBounds(7, -1000.0 * KS, KS)
    if closed:
        for q in nons: h.changeCoeff(q, 7, 1.0)
    h.run(); st = h.getModelStatus(); res = None
    if st == _core.HighsModelStatus.kOptimal:
        sol = h.getSolution(); res = (float(sol.col_value[7]) / KS, list(sol.row_dual), list(sol.col_dual), list(sol.col_value))
    if closed:
        for q in nons: h.changeCoeff(q, 7, 0.0)
    h.changeColBounds(7, -KS, KS)
    S.nlp += 1
    return res

def farkas(S, lo, hi):
    """exact certificate of infeasibility of the exact system at the current stack, or None"""
    rows = exact_rows(S, lo, hi); nrow = len(S.ex)
    for closed in (True, False):
        res = lp_duals(S, closed)
        if res is None: continue
        t, rd, cd, cv = res
        if closed and t >= -1e-12: continue
        lam = [0.0] * len(rows)
        for q in range(nrow): lam[q] = max(0.0, -rd[q])
        for j in range(1, 7):
            d = cd[j]
            if d > 0: lam[nrow + 2 * (j - 1)] = d        # lower bound row
            elif d < 0: lam[nrow + 2 * (j - 1) + 1] = -d  # upper bound row
        mx = max(lam) if lam else 0
        if mx <= 0: continue
        sup = [q for q in range(len(rows)) if lam[q] > 1e-9 * mx]
        guess = [F(lam[q]).limit_denominator(10**9) for q in sup]
        C = [([rows[q][0][i] for q in sup], F(0)) for i in range(6)]
        for with_rhs in (False, True):
            A = list(C)
            if with_rhs: A = A + [([rows[q][1] for q in sup], F(0))]
            lm = _project(guess, A, len(sup))
            if lm is None or any(v < 0 for v in lm): continue
            tot = sum(l * rows[q][1] for l, q in zip(lm, sup))
            smass = sum(l for l, q in zip(lm, sup) if rows[q][2])
            if any(sum(l * rows[q][0][i] for l, q in zip(lm, sup)) != 0 for i in range(6)): continue
            if tot < 0 or (tot == 0 and smass > 0): return ('closed' if tot < 0 else 'strict', len(sup))
    return None

def cert_arr(cell, c, rho):
    if rho is None or any(rho[i] >= rho[i + 1] for i in range(6)) or rho[6] > cell.W: return None
    o = outcome(rho)
    if o['opener'] and o['opener'][0] == cell.s[cell.m] + 1 and o['closer'][0] == c + 1: return rho, o
    return None

def exact_options(cell, k, y, final, lo, hi):
    s = cell.s[k]; cc = 8 * cell.j[k] + 1
    umin = cc * lo[y] / hi[s]; umax = cc * hi[y] / lo[s]; out = []
    for l in range(0, int(umax // 8) + 2):
        if 8 * l + 7 >= umin and 8 * l + 1 <= umax: out.append(('G', l))
        if not final and l >= 1 and 8 * l + 1 >= umin and 8 * l - 1 <= umax: out.append(('B', l))
    return out


def node_box(path, J, certify=True, pad=F(1, 10**7)):
    """box of the readings over the RELAXATION of the node (path prefix): setter-blocked rows + order + window.  Float LP bounds, padded, then each
    bound certified exactly by Farkas against the relaxation (uncertified bounds fall back to the window edge).  returns (box list of (lo, hi) floats, n_cert, n_fail)"""
    W = 8 * J + 1
    cell0 = Cell(path, [(1.0, float(W))] * 7, J); S0 = setup(cell0); h = S0.h
    lo0, hi0 = exact_bounds(cell0)
    box = [(1.0, 1.0)]; ncert = 0; nfail = 0
    for j in range(1, 7):
        res = []
        for sgn in (1.0, -1.0):
            for q in range(8): h.changeColCost(q, 0.0)
            h.changeColCost(j, sgn); h.run()
            x = np.array(h.getSolution().col_value) / KS
            res.append(float(x[j]))
        for q in range(8): h.changeColCost(q, -1.0 if q == 7 else 0.0)
        l, u = res[0], res[1] if False else res[1]
        # res[0] = min x_j, res[1] = max of (-x_j) minimised => min(-x_j) => value -max ; recompute
        l = res[0]; u = -res[1] if False else res[1]
        box.append((l, u))
    # res[1] was computed minimising -x_j, so its x_j IS the maximiser: u = res[1]
    out = [(1.0, 1.0)]
    for j in range(1, 7):
        l, u = box[j]
        lo_e = F(l) - pad; hi_e = F(u) + pad
        okl = okh = False
        if certify:
            mk = S0.mark(); S0.add({j: -1}, -hi_e if False else -(hi_e), False)   # x_j >= hi_e  (should be infeasible)
            okh = farkas(S0, lo0, hi0) is not None; S0.rollback(mk)
            mk = S0.mark(); S0.add({j: 1}, lo_e, False)                            # x_j <= lo_e (should be infeasible below lo_e - ... )
            # lower bound claim: x_j >= lo_e  <=>  infeasible(x_j < lo_e): test strict row x_j <= lo_e - tiny is wrong; use x_j <= lo_e and check farkas of (x_j <= lo_e) is infeasible only if lo_e < min; use strict
            S0.rollback(mk)
            mk = S0.mark(); S0.add({j: 1}, lo_e, True)
            okl = farkas(S0, lo0, hi0) is not None; S0.rollback(mk)
            ncert += int(okl) + int(okh); nfail += int(not okl) + int(not okh)
        out.append((float(lo_e) if (okl or not certify) else 1.0, float(hi_e) if (okh or not certify) else float(W)))
    return out, ncert, nfail

def decide_node_all(path, J, budget1=400):
    """pass 1 (window box, no float data) for all 7 closers on one shared stack; closers that hit the budget get pass 2 (certified relaxation box)"""
    W = float(8 * J + 1); cell = Cell(path, [(1.0, W)] * 7, J); S = setup(cell); lo, hi = exact_bounds(cell); out = {}
    for c in range(7):
        v, st, nlp = decide_exact(path, None, J, c, budget1, shared=(cell, S, lo, hi))
        st['pass'] = 1
        if v == 'BUDGET': v, st, nlp2 = decide_node(path, J, c)
        out[c] = (v, st)
    return out

def decide_node(path, J, c, node_budget=8000, certify=True):
    """pass 1: window box only (no float data anywhere), small budget; pass 2 (if pass 1 hits its budget): exactly-certified relaxation box"""
    W = float(8 * J + 1)
    v, st, nlp = decide_exact(path, [(1.0, W)] * 7, J, c, 400)
    st['box_cert'] = 0; st['box_fail'] = 0; st['pass'] = 1
    if v != 'BUDGET': return v, st, nlp
    box, nc, nf = node_box(path, J, certify)
    v2, st2, nlp2 = decide_exact(path, box, J, c, node_budget)
    st2['box_cert'] = nc; st2['box_fail'] = nf; st2['pass'] = 2
    return v2, st2, nlp + nlp2


def decide_exact(path, box, J, c, node_budget=4000, shared=None):
    if shared is None:
        cell = Cell(path, box, J); S = setup(cell); lo, hi = exact_bounds(cell)
    else: cell, S, lo, hi = shared
    m = cell.m; base_mark = S.mark(); nlp0 = S.nlp
    st = {'nodes': 0, 'cert_closed': 0, 'cert_strict': 0, 'interval': 0, 'uncert': 0, 'over': False, 'feas': None, 'leaves_exact_witness': 0}
    # decision order: final laps (target c first), then intermediates
    fin = [(m, y, True) for y in range(7) if y != cell.s[m]]
    fin.sort(key=lambda d: 0 if d[1] == c else 1)
    inter = [(k, y, False) for k in range(m) for y in range(7) if y != cell.s[k] and y != cell.s[k + 1]]
    import os
    if os.environ.get('SP_ORDER','rev')=='rev': inter = inter[::-1]
    dec = fin + inter
    laps = {cell.s[m]: cell.j[m]}
    import os as _os
    if c == cell.s[m] and _os.environ.get('SP_LEMMA') == '1':
        S.add({6: 3, cell.s[m]: -4}, 0, False)     # Lemma L: closer = opener  =>  3 rho_7 <= 4 rho_s
    def pair_rows(y_new):
        """closer rows between c and a newly decided final reading (or both fixed at start)"""
        if y_new == c:
            for y in laps:
                if y != c: S.add({y: 8 * laps[c] + 7, c: -(8 * laps[y] + 7)}, 0, y < c)
        elif c in laps:
            y = y_new; S.add({y: 8 * laps[c] + 7, c: -(8 * laps[y] + 7)}, 0, y < c)
    # at start, c may be the final setter (lap fixed) : add rows for already-known laps
    if c in laps: pair_rows(c) if False else None
    def start_rows():
        if c == cell.s[m]:
            pass
    def prune_check(r):
        """returns True if node is excluded (certified)"""
        if r is not None and r[0] > TOL: return False
        cert = farkas(S, lo, hi)
        if cert is not None:
            st['cert_closed' if cert[0] == 'closed' else 'cert_strict'] += 1; return True
        return False
    def feasible_witness():
        rho, info = interior_exact(S)
        if rho is None:
            rho = polish(S)
        cr = cert_arr(cell, c, rho)
        return cr
    def rec(i):
        if st['nodes'] > node_budget: st['over'] = True; return False
        if i == len(dec):
            r = S.solve()
            if r is not None and r[0] > TOL:
                cr = feasible_witness()
                if cr is not None: st['feas'] = (cr[0], cr[1]['path'] == tuple(path)); return True
                st['uncert'] += 1; return False
            if prune_check(r): return False
            cr = feasible_witness()
            if cr is not None: st['feas'] = (cr[0], cr[1]['path'] == tuple(path)); return True
            st['uncert'] += 1; return False
        k, y, final = dec[i]
        opts = exact_options(cell, k, y, final, lo, hi)
        if not opts: st['interval'] += 1; return False
        for (t, l) in opts:
            mk = S.mark()
            (add_G if t == 'G' else add_B)(S, k, y, l)
            if final:
                laps[y] = l; pair_rows(y)
            st['nodes'] += 1
            r = S.solve()
            if not prune_check(r):
                if rec(i + 1):
                    S.rollback(mk)
                    if final: del laps[y]
                    return True
            if final: del laps[y]
            S.rollback(mk)
        return False
    # target c is the final setter: nothing to decide for its lap; rows against others are added as the others are decided
    if c == cell.s[m]:
        pass
    # when c is the final setter, pair rows are added when each y is decided (c in laps already)
    ok = rec(0)
    S.rollback(base_mark)
    verdict = 'FEAS' if st['feas'] else ('BUDGET' if st['over'] else ('UNCERT' if st['uncert'] else 'INF'))
    return verdict, st, S.nlp - nlp0

if __name__ == '__main__':
    J = int(sys.argv[1]); c = int(sys.argv[2]) - 1; a = int(sys.argv[3]); b = int(sys.argv[4])
    T = pickle.load(open(f'terminals5_J{J}.pkl', 'rb'))
    for i in range(a, b):
        p, lo_, hi_, box, w = T[i]
        t0 = time.time(); v, st, nlp = decide_exact(p, box, J, c)
        print(i, 'opener', p[-1][0], 'closer', c + 1, v, {k: x for k, x in st.items() if k != 'feas'}, 'path_equal' if st['feas'] and st['feas'][1] else '', 'nlp', nlp, round(time.time() - t0, 2), flush=True)
