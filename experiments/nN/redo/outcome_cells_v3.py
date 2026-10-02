# For every stored terminal cell: find an EXACT interior point (Fractions, checked against the cell's own exact constraints),
# run the exact cascade there, compare its path with the cell's path, and record the outcome.
import sys, pickle
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
J = int(sys.argv[1]); RHOMAX = 8 * J + 1
T = pickle.load(open('terminals6_J%d.pkl' % J, 'rb'))
def exact_ok(cons, v):
    for ec, ec0, strict in cons:
        s = ec0 + sum(c * x for c, x in zip(ec, v))
        if (s <= 0) if strict else (s < 0): return False
    return True
def refit(cons):
    """maximum-slack interior point with tight tolerances; returns list of floats or None"""
    NV = 6; A = []; b = []
    for ec, ec0, strict in cons:
        c = np.array([float(x) for x in ec]); nrm = float(np.linalg.norm(c)) or 1.0
        A.append(list(-c) + [nrm if strict else 0.0]); b.append(float(ec0))
    res = linprog([0.0] * NV + [-1.0], A_ub=np.array(A), b_ub=np.array(b), bounds=[(0, RHOMAX + 1)] * NV + [(0, 1)], method="highs-ds",
                  options=dict(primal_feasibility_tolerance=1e-10, dual_feasibility_tolerance=1e-10))
    return (res.x[:NV], res.x[-1]) if res.status == 0 else (None, 0.0)
rows = []; stat = {"exact pt, path matches": 0, "exact pt, path differs": 0, "no exact pt": 0}; thin = []
for (p, lo, hi, rng_, w, cons) in T:
    pt = None
    for D in (None, 10**9, 10**12, 10**15):
        v = w if w is not None else None
        if v is None: break
        cand = [F(1)] + [F(x) if D is None else F(x).limit_denominator(D) for x in v]
        if exact_ok(cons, cand[1:]): pt = cand; break
    if pt is None:
        v, t = refit(cons)
        if v is not None:
            for D in (None, 10**12, 10**15):
                cand = [F(1)] + [F(x) if D is None else F(x).limit_denominator(D) for x in v]
                if exact_ok(cons, cand[1:]): pt = cand; break
    if pt is None: stat["no exact pt"] += 1; thin.append(p); continue
    o = outcome(pt)
    if o['path'] == tuple(p): stat["exact pt, path matches"] += 1
    else: stat["exact pt, path differs"] += 1
    o['cell'] = p; o['rho'] = pt; o['lo'] = lo; o['hi'] = hi; o['ok'] = (o['path'] == tuple(p)); rows.append(o)
print("J", J, "cells", len(T), stat)
pickle.dump(rows, open('outcome_cells_v3_J%d.pkl' % J, 'wb'))
