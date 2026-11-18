# conjT3_boxcheck2_v1 -- the corrected chamber-level collapse.
# Within a chamber (ratio-bounded region of a skeleton cell-box), the component's
# boundary assignment (rho_L,k_L),(rho_R,k_R) is stable and q = rho_L/rho_R ranges over
# [c, q_box_max] where c is the binding hyperplane constant (or the cell bound).
# Chamber death (sufficient + observed-tuple-complete):
#   D1: q_min_chamber >= 9*phi/7          (J=0 at every tuple: no band ever opens)
#   D2: (8*J(q_min_chamber)+1)*rho_R_max <= 25*(8k_R-1)
# Chamber partition of a cell-box: hyperplanes rho_L/rho_R = c for the boundary
# assignments' thresholds (9*phi/7 per (kL,kR)) + the zone-edge ratios.  For SCOPING
# we verify the OBSERVED-TUPLE certificate is implied: every observed dead tuple's
# (q_tuple, kL, kR, rho_R_tuple) must satisfy D1 or D2 in ITS chamber.
import itertools
from fractions import Fraction as F
from taillemma_lib_v1 import zones_of
from conjT3_enum_v1 import k6_components, race_certificate, column_state, skels

CELLS = ['P','S1','G1','S2','E']
CELLBOUNDS = {'P': (F(1),F(7)), 'S1': (F(7),F(9)), 'G1': (F(9),F(15)), 'S2': (F(15),F(17)), 'E': (F(17),F(17))}
def cell_of(x):
    if x <= F(7): return 'P'
    if x < F(9): return 'S1'
    if x <= F(15): return 'G1'
    if x < F(17): return 'S2'
    return 'E'

def J_of(q, kL, kR, cap=30000):
    phi = F(8*kL+1, 8*kR-1)
    if q <= phi: return None
    j = 1; J = 0
    while F(8*j-1)*q < F(8*j+1)*phi:
        J = j; j += 1
        if j > cap: return cap
    return J

def phi_of(kL, kR): return F(8*kL+1, 8*kR-1)

# For each observed COMP-DEAD certificate, compute its chamber's q-lower-bound:
# the largest threshold among {9*phi/7 (this assignment)} and the cell-ratio bounds
# (rho_L >= cellmin(L-cell), rho_R <= cellmax(R-cell) give q >= cellmin/cellmax).
# D1 uses the binding q_min = max(9*phi/7 if positive-side, cellmin/cellmax) — but the
# TRUE chamber bound comes from the hyperplane that BOUNDS THE CHAMBER BELOW; without
# the full hyperplane arrangement we use the conservative bound q_min = cellmin/cellmax
# AND additionally test the tuple's own q.  The chamber claim verified here:
#   D2 with J(q_min_box) OR D1-with-threshold-at-tuple-q... 
# The honest testable version now: for the observed tuple's certificate, is the death
# explained by the TWO-LINE rule evaluated at the CHAMBER-reachable q-interval
# [q_tuple_reachable_min, q_box_max] where q_tuple_reachable_min = cellmin/cellmax?
# i.e. does the rule fire for EVERY q in that interval?  Sweep q over the interval at
# its endpoints + threshold crossings (the rule is monotone-ish in q: J decreasing).
# Death-for-all-q-in-interval test:
#   for q in interval: dead(q) := J(q)==0 or (8*J(q)+1)*rhoRmax <= 25*(8kR-1)
# J(q) decreasing in q, so the binding q is the MINIMUM q of the interval for D2, and
# D1 fires iff q_min >= 9phi/7.  So the interval test IS the 2-line test — v1 was right
# for a FIXED (rhoL-cell, rhoR-cell) pair; v1 failed because q_min = cellmin/cellmax
# is far below the tuple's q.  CORRECT v2: the chamber's q-min is NOT cellmin/cellmax —
# it is bounded below by the hyperplanes that SEPARATE the boundary zones: within the
# cell-box, the component's exit a is the boundary of zones (8k_L±1)/rho_L etc.  The
# chamber q-interval is [c, qmax] with c from the NEAREST other zone-edge ratio.
# SCOPING v2: compute, for each observed certificate, the true chamber lower bound c:
#   c = min over the box of rho_L/rho_R SUBJECT TO the same boundary assignment —
# the assignment changes when rho_L crosses a zone edge of ITS OWN reading... 
# Practical exact bound: the boundary zone Z(rho_L,k_L) has edges (8k_L-1)/rho_L, 
# (8k_L+1)/rho_L; the component edge a = one of them; for a to REMAIN the k_L-th zone's
# edge while rho_L ranges over its cell: a in [(8k_L-1)/rho_L, (8k_L+1)/rho_L] gives
# rho_L in [(8k_L-1)/a, (8k_L+1)/a] ∩ cell_L.  Similarly rho_R in [(8k_R-1)/b,(8k_R+1)/b] ∩ cell_R.
# Then q_min = max((8kL-1)/a, cellmin_L) / min((8kR+1)/b, cellmax_R) with a,b the
# component edges — and a,b are THEMSELVES functions of the other readings... 
# We use the tuple's a,b (fixed within the chamber's finer partition) as the scope.
def chamber_test(cert, rhoL_cell, rhoR_cell, a, b, rlo=F(25)):
    if 'note' in cert: return ('boundary', None)
    rLs, kL = cert['L']; rRs, kR = cert['R']
    rL, rR = F(rLs), F(rRs)
    cL_lo, cL_hi = CELLBOUNDS[rhoL_cell]; cR_lo, cR_hi = CELLBOUNDS[rhoR_cell]
    # chamber bounds from the zone-edge structure at the tuple's component edges
    rhoL_lo = max(cL_lo, F(8*kL-1)/a); rhoL_hi = min(cL_hi, F(8*kL+1)/a)
    rhoR_lo = max(cR_lo, F(8*kR-1)/b); rhoR_hi = min(cR_hi, F(8*kR+1)/b)
    if rhoL_lo > rhoL_hi or rhoR_lo > rhoR_hi: return ('degenerate', None)
    q_min = rhoL_lo / rhoR_hi
    q_max = rhoL_hi / rhoR_lo
    phi = phi_of(kL, kR)
    thr = 9*phi/7
    # D1: entire chamber q >= thr?
    if q_min >= thr: return ('D1', q_min)
    # D2: (8*J(q_min)+1)*rhoR_hi <= rlo*(8kR-1)?
    Jm = J_of(q_min, kL, kR)
    if Jm is None: return ('qle-phi', q_min)
    if F(8*Jm+1)*rhoR_hi <= rlo*F(8*kR-1): return ('D2', q_min)
    return ('OPEN', (q_min, q_max, str(rhoR_hi)))

import random
random.seed(3)
RLO = F(25)
tally = {}
examples = {}
for s in skels:
    vals = []
    for c in s:
        lo, hi = CELLBOUNDS[c]
        cand = sorted(set([lo, hi] + ([F(2*(int(lo*5)+i),10) for i in range(int(hi*5)-int(lo*5)+1)] if lo != hi else [])))
        vals.append(cand)
    for rho in itertools.product(*vals):
        if any(rho[i] > rho[i+1] for i in range(4)): continue
        dead, info = column_state(list(rho), RLO, F(50))
        if not dead or info is None or info['kind'] != 'COMP-DEAD': continue
        cert = info['cert']
        if cert is None: continue
        i = info['idx']
        comps = k6_components(list(rho))
        a, b = comps[i]
        # the boundary readings' cells
        rLs, kL = cert['L']; rRs, kR = cert['R']
        if 'note' in cert: key = 'boundary'; tally[key] = tally.get(key,0)+1; continue
        cL, cR = cell_of(F(rLs)), cell_of(F(rRs))
        verdict, aux = chamber_test(cert, cL, cR, a, b)
        tally[verdict] = tally.get(verdict, 0) + 1
        if verdict == 'OPEN' and verdict not in examples:
            examples[verdict] = (s, cert['L'], cert['R'], str(a), str(b), aux)
        if verdict not in tally or tally[verdict] == 1:
            pass
print("chamber-level death tally:", tally)
for k, v in examples.items():
    print("  example", k, ":", v)
