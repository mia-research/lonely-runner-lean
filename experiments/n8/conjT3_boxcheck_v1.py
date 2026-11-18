# conjT3_boxcheck_v1 -- box-level death re-check: does each observed COMP-DEAD
# certificate hold over the WHOLE skeleton cell box (not just the sampled tuple)?
# Two-line sufficient check: J <= J(q_min) with q_min = min rho_L / max rho_R over
# the box (J decreasing in q); death if (8J*+1) * max(rho_R) <= 25*(8kR-1).
import random, itertools
from fractions import Fraction as F
from taillemma_lib_v1 import zones_of
from conjT3_enum_v1 import k6_components, race_certificate, column_state, skels
CELLS = ['P','S1','G1','S2','E']
CELLBOUNDS = {'P': (F(10,10),F(7)), 'S1': (F(7),F(9)), 'G1': (F(9),F(15)), 'S2': (F(15),F(17)), 'E': (F(17),F(17))}

random.seed(3)
RLO = F(25)

def cell_max(c): return CELLBOUNDS[c][1]
def cell_min(c): return CELLBOUNDS[c][0]

def J_of(q, kL, kR, cap=20000):
    phi = F(8*kL+1, 8*kR-1)
    if q <= phi: return None  # degenerate: a >= b cannot happen for a component; treat as inf
    j = 1; J = 0
    while F(8*j-1)*q < F(8*j+1)*phi:
        J = j; j += 1
        if j > cap: return cap
    return J

def box_death(cL, cR, kL, kR):
    """Sufficient box-uniform death: True/False + J*."""
    q_min = cell_min(cL) / cell_max(cR)
    Jstar = J_of(q_min, kL, kR)
    if Jstar is None: return (False, None)   # q_min <= phi: J unbounded on box -> check fails
    rR_max = cell_max(cR)
    ok = F(8*Jstar+1) * rR_max <= RLO * F(8*kR-1)
    return (ok, Jstar)

# re-run P1 probes; for every COMP-DEAD kill, verify box-level death of its certificate
pass_box = fail_box = 0
failures = []
cell_of_cache = {}
def cell_of_val(x):
    if x <= F(7): return 'P'
    if x < F(9): return 'S1'
    if x <= F(15): return 'G1'
    if x < F(17): return 'S2'
    return 'E'

import itertools as it
for s in skels:
    vals = []
    for c in s:
        lo, hi = CELLBOUNDS[c]
        # representative + extremes
        cand = sorted(set([lo, hi] + ([F(2*(int(lo*5)+i), 10) for i in range(int(hi*5)-int(lo*5)+1)] if lo != hi else [])))
        vals.append(cand)
    for rho in it.product(*vals):
        if any(rho[i] > rho[i+1] for i in range(4)): continue
        dead, info = column_state(list(rho), RLO, F(50))
        if not dead or info is None: continue
        if info['kind'] != 'COMP-DEAD': continue
        cert = info['cert']
        if cert is None or 'note' in cert: continue
        rLs, kL = cert['L']; rRs, kR = cert['R']
        rL, rR = F(rLs), F(rRs)
        cL, cR = cell_of_val(rL), cell_of_val(rR)
        ok, Jstar = box_death(cL, cR, kL, kR)
        if ok: pass_box += 1
        else:
            fail_box += 1
            if len(failures) < 12:
                failures.append((s, (str(rL),kL,cL), (str(rR),kR,cR), 'tupleJ', cert['J'], 'boxJ*', Jstar))

print("COMP-DEAD certificates box-uniform: PASS %d | FAIL %d" % (pass_box, fail_box))
for f in failures: print("  FAIL:", f)
