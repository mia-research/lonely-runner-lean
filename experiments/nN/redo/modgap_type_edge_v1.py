"""modgap_type_edge_v1 (2026-10-06): the exact edge in rho_min of every failing move type of the arc criterion in a slab, by the tree of modgap_tree_v1 (imported unchanged)
with per-reading bounds, then one linear programme per FAIL cell certified exactly.

Object (as modgap_tree_v1): six readings rho_0 < ... < rho_5 (ratios to d_min), the 1/7-cascade of the six in u = 7*m*t from u = 1; a FAIL cell is a set of
arrangements following one path of setters and zones whose last exit is above 6 (the arc u in [1, 6] holds no lonely instant of the six).
Slab: A <= rho_0 <= B and A <= rho_i <= RMAX for the others.  The tree enumerates every path in the slab (float LPs steer the feasibility of cells;
the pruned branches carry no exact certificate: [TREE]).
For each FAIL cell C (its path inequalities, strict ones closed): sup of rho_min = min_k rho_k over closure(C) intersected with {rho_i <= RMAX}, with no lower
bound A or upper bound B on rho_0, as a linear programme.  Certified EXACTLY: (i) dual multipliers y >= 0 on the support found by the float solver, solved
in Fractions so that sum y_i a_i = e_z, giving z <= sum y_i b_i for every point of the closed cell; (ii) a primal point of the closed cell with z equal to
that bound, solved in Fractions and checked against every inequality.  Both found: the sup is exact.  Whether rho_i <= RMAX is in the dual support is
reported (if it is, a larger RMAX can raise the sup).
[PROVISIONAL: covering; supports: the exact edge in rho_min of each failing move type found in the slab, and their maximum as the boundary rho* of the
arc criterion inside the slab's reach; not an existence claim]  [TREE: float-LP enumeration, exact certificates for each FAIL cell's edge only].
Usage: python3 modgap_type_edge_v1.py A B RMAX TAG"""
import sys, time, json
from fractions import Fraction as F
A_, B_, RMAX_, TAG_ = F(sys.argv[1]), F(sys.argv[2]), F(sys.argv[3]), sys.argv[4]
sys.argv = ['modgap_tree_v1.py', str(A_), str(RMAX_), '80', 'unused']
import modgap_tree_v1 as T
T.BOUNDS = [(float(A_), float(B_))] + [(float(A_), float(RMAX_))] * 5 + [(1.0, 1.0)]
import numpy as np
from scipy.optimize import linprog
import sympy

def edge(cons):
    """sup of min rho over the closed cell, rho_i <= RMAX, rho_6 = 1.  Rows: a.x <= b over x = (rho_0..rho_5, z)."""
    rows = []; tags = []
    for k in cons:                                   # k.ec . (rho_0..rho_6) >= 0  ->  -(sum_{i<6} c_i rho_i) <= c_6
        c = k.ec
        rows.append(([-c[i] for i in range(6)] + [F(0)], c[6])); tags.append('cell')
    for i in range(6):
        a = [F(0)] * 7; a[i] = F(1); rows.append((a, RMAX_)); tags.append('rho_%d <= RMAX' % i)
        a = [F(0)] * 7; a[i] = F(-1); rows.append((a, F(0))); tags.append('rho_%d >= 0' % i)
        a = [F(0)] * 7; a[6] = F(1); a[i] = F(-1); rows.append((a, F(0))); tags.append('z <= rho_%d' % i)
    Af = np.array([[float(v) for v in a] for a, b in rows]); bf = np.array([float(b) for a, b in rows])
    res = linprog([0] * 6 + [-1], A_ub=Af, b_ub=bf, bounds=[(None, None)] * 7, method='highs')
    if res.status != 0: return None
    yf = -res.ineqlin.marginals
    sup = [i for i in range(len(rows)) if yf[i] > 1e-10]
    # exact dual on the support
    ys = sympy.symbols('y0:%d' % len(sup))
    eqs = []
    for t in range(7):
        target = 1 if t == 6 else 0
        eqs.append(sum(ys[s] * sympy.Rational(rows[i][0][t].numerator, rows[i][0][t].denominator) for s, i in enumerate(sup)) - target)
    sol = sympy.linsolve(eqs, ys)
    yex = None
    for s_ in sol:
        free = set().union(*[v.free_symbols for v in s_])
        if free:      # fix free multipliers at their float values, rationalised, then re-solve
            sub = {f: sympy.Rational(str(F(float(yf[sup[ys.index(f)]])).limit_denominator(10**6))) for f in free}
            s_ = [v.subs(sub) for v in s_]
        cand = [F(int(sympy.fraction(v)[0]), int(sympy.fraction(v)[1])) for v in s_]
        if all(v >= 0 for v in cand): yex = cand
    if yex is None: return {'float': res.x[6], 'certified': False}
    chk = [sum(yex[s] * rows[i][0][t] for s, i in enumerate(sup)) for t in range(7)]
    assert chk == [F(0)] * 6 + [F(1)]
    bound = sum(yex[s] * rows[i][1] for s, i in enumerate(sup))
    # exact primal: the support's constraints active and z = bound; free coordinates from the float optimum
    xs = sympy.symbols('x0:7')
    peqs = [sum(sympy.Rational(rows[i][0][t].numerator, rows[i][0][t].denominator) * xs[t] for t in range(7)) - sympy.Rational(rows[i][1].numerator, rows[i][1].denominator) for i in sup]
    peqs.append(xs[6] - sympy.Rational(bound.numerator, bound.denominator))
    psol = sympy.linsolve(peqs, xs); pt = None
    for s_ in psol:
        free = set().union(*[v.free_symbols for v in s_])
        if free:
            sub = {f: sympy.Rational(str(F(float(res.x[xs.index(f)])).limit_denominator(10**4))) for f in free}
            s_ = [v.subs(sub) for v in s_]
        pt = [F(int(sympy.fraction(v)[0]), int(sympy.fraction(v)[1])) for v in s_]
    ok = pt is not None and all(sum(a[t] * pt[t] for t in range(7)) <= b for a, b in rows)
    return {'float': res.x[6], 'certified': True, 'sup': bound, 'primal_ok': ok, 'point': pt,
            'support': [tags[i] for i in sup], 'rmax_active': any(tags[i].endswith('RMAX') for i in sup),
            'support_rows': [([str(v) for v in rows[i][0][:6]], str(rows[i][1])) for i in sup if tags[i] == 'cell']}

if __name__ == '__main__':
    out = open('modgap_type_edge_v1_%s.out' % TAG_, 'w'); out.write(__doc__ + "\n")
    def log(s): out.write(s + "\n"); out.flush(); print(s, flush=True)
    log("slab: %s <= rho_0 <= %s, others in [%s, %s]" % (A_, B_, A_, RMAX_))
    T.R0 = A_
    t0 = time.time()
    T.expand(T.root(), 6, 0, [], 0)
    log("tree DONE: nodes %d, deepest %d, FAIL cells %d, cut nodes %d, %.0fs" % (T.nodes, T.maxdepth, len(T.fails), len(T.cut), time.time() - t0))
    best = None; recs = []
    for idx, (path, cons, pt) in enumerate(T.fails):
        ec = T.exact_check(pt)
        e = edge(cons)
        rec = {'idx': idx, 'path': path, 'witness_exact_cascade': (ec[0], str(ec[1]), [str(v) for v in ec[2]]) if ec else None}
        if e and e.get('certified'):
            rec.update({'sup_rho_min': str(e['sup']), 'primal_ok': e['primal_ok'], 'rmax_active': e['rmax_active'],
                        'point': [str(v) for v in e['point']] if e['point'] else None, 'support': e['support'], 'support_rows': e['support_rows']})
            if e['primal_ok'] and (best is None or e['sup'] > best[0]): best = (e['sup'], idx)
        else:
            rec['sup_rho_min'] = None; rec['float'] = e['float'] if e else None
        recs.append(rec)
        log("FAIL %d: path %s" % (idx, path))
        log("   witness exact cascade (lands <= 6?, landing, rho): %s" % (rec['witness_exact_cascade'],))
        log("   sup rho_min over the closed cell (rho_i <= RMAX): %s ; primal point checked: %s ; RMAX in the dual support: %s" % (rec.get('sup_rho_min'), rec.get('primal_ok'), rec.get('rmax_active')))
        if rec.get('support_rows') is not None: log("   binding cell inequalities (a.rho <= b, rho_6 = 1 folded into b): %s" % rec['support_rows'])
    log("max certified sup of rho_min over the FAIL cells of this slab: %s (cell %s)" % (best[0] if best else None, best[1] if best else None))
    json.dump(recs, open('modgap_type_edge_v1_%s.json' % TAG_, 'w'))
    out.close()
