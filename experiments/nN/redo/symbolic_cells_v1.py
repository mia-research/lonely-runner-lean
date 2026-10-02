# EXHAUSTION BY CELLS (prototype).  Arrangement = readings rho_1 = 1 < rho_2 < ... < rho_7 <= RHOMAX (= 8*J + 1).  The cascade is run SYMBOLICALLY:
# at a state with definer (x, J)  (R = (8J+1)/rho_x; start: x = 1, J = 0) every other reading y has position u = (8J+1) rho_y / rho_x, and is
#   clear on W_j = [8j+1, 8j+7]   or a blocker on B_j = (8j-1, 8j+1)   -- each a pair of LINEAR inequalities in rho (strict for B, non-strict for W);
# the setter is the blocker with the largest end (8j+1)/rho_y (ties: larger index wins, as in the exact cascade); next state = its exit.
# A branch is kept iff its cell has an interior point (LP, maximal slack on the strict inequalities).  A leaf = no blocker.
# Soundness: an exact rational witness of every leaf is run through the exact cascade.  Coverage: random exact arrangements must lie in exactly one leaf.
import sys, math, time, random, itertools
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
J_W = int(sys.argv[1]) if len(sys.argv) > 1 else 1
RHOMAX = 8 * J_W + 1
NV = 6                      # variables rho_2 .. rho_7
def lin(a):                 # a = coefficients of rho_1..rho_7 (Fractions); rho_1 = 1
    return ([float(x) for x in a[1:]], float(a[0]), [x for x in a[1:]], a[0])
class Con:
    __slots__ = ("c", "c0", "strict", "ec", "ec0", "norm")
    def __init__(self, a, strict):
        self.c = np.array([float(x) for x in a[1:]]); self.c0 = float(a[0]); self.strict = strict
        self.ec = [F(x) for x in a[1:]]; self.ec0 = F(a[0]); self.norm = float(np.linalg.norm(self.c)) or 1.0
    def exact(self, v):
        s = self.ec0 + sum(c * x for c, x in zip(self.ec, v))
        return s > 0 if self.strict else s >= 0
def vec(idx_coef):
    a = [F(0)] * 7
    for i, c in idx_coef: a[i] += F(c)
    return a
def feasible(cons):
    # variables v (6) and slack t:   c.v + c0 - t*norm >= 0 (strict), c.v + c0 >= 0 (non-strict); maximise t
    A = []; b = []
    for k in cons:
        row = list(-k.c) + [k.norm if k.strict else 0.0]; A.append(row); b.append(k.c0)
    cobj = [0.0] * NV + [-1.0]
    res = linprog(cobj, A_ub=np.array(A), b_ub=np.array(b), bounds=[(0, RHOMAX + 1)] * NV + [(0, 1)], method="highs")
    if res.status != 0: return False, None
    t = res.x[-1]
    any_strict = any(k.strict for k in cons)
    if any_strict and t < 1e-9: return False, None
    return True, res.x[:NV]
def rng(cons, i):
    A = [list(-k.c) for k in cons]; b = [k.c0 for k in cons]
    out = []
    for sgn in (1, -1):
        cobj = [0.0] * NV; cobj[i] = sgn
        res = linprog(cobj, A_ub=np.array(A), b_ub=np.array(b), bounds=[(0, RHOMAX + 1)] * NV, method="highs")
        out.append(res.x[i] if res.status == 0 else None)
    return out[0], out[1]
def rho_range(cons, y):
    return (1.0, 1.0) if y == 0 else rng(cons, y - 1)
nodes = 0; leaves = []; deepest = 0
def slabs_for(cons, x, J, y, ranges):
    """feasible statuses of reading y at the state (x, J): list of (kind, j, newcons)"""
    lo_y, hi_y = ranges[y]; lo_x, hi_x = ranges[x]
    umin = (8 * J + 1) * lo_y / hi_x; umax = (8 * J + 1) * hi_y / lo_x
    out = []
    jmin = max(0, int((umin - 7) // 8)); jmax = int(umax // 8) + 1
    for j in range(jmin, jmax + 1):
        # clear W_j : (8J+1) rho_y - (8j+1) rho_x >= 0 ; (8j+7) rho_x - (8J+1) rho_y >= 0
        new = [Con(vec([(y, 8 * J + 1), (x, -(8 * j + 1))]), False), Con(vec([(x, 8 * j + 7), (y, -(8 * J + 1))]), False)]
        ok, _ = feasible(cons + new)
        if ok: out.append(("clear", j, new))
        if j >= 1:
            new = [Con(vec([(y, 8 * J + 1), (x, -(8 * j - 1))]), True), Con(vec([(x, 8 * j + 1), (y, -(8 * J + 1))]), True)]
            ok, _ = feasible(cons + new)
            if ok: out.append(("block", j, new))
    return out
def expand(cons, x, J, path, depth):
    global nodes, deepest
    nodes += 1; deepest = max(deepest, depth)
    if nodes % 200 == 0: print("   nodes %d, leaves %d, depth %d, %.0fs" % (nodes, len(leaves), deepest, time.time() - t0), file=sys.stderr, flush=True)
    if depth > 40: leaves.append(("DEPTH", path, cons)); return
    ranges = {y: rho_range(cons, y) for y in range(7)}
    others = [y for y in range(7) if y != x]
    # choose a status for each other reading, depth-first with feasibility pruning
    def rec(i, cur, status):
        if i == len(others):
            blockers = [(y, status[y][1]) for y in others if status[y][0] == "block"]
            if not blockers:
                leaves.append(("LEAF", path, cur, (x, J))); return
            # the setter: largest end (8j+1)/rho_y ; ties -> larger index
            for w, jw in blockers:
                new = []
                for z, jz in blockers:
                    if z == w: continue
                    # E_w >= E_z (z < w) : (8jw+1) rho_z - (8jz+1) rho_w >= 0 ; E_w > E_z (z > w) strict
                    new.append(Con(vec([(z, 8 * jw + 1), (w, -(8 * jz + 1))]), z > w))
                ok, _ = feasible(cur + new) if new else (True, None)
                if ok: expand(cur + new, w, jw, path + [(w + 1, jw)], depth + 1)
            return
        y = others[i]
        for kind, j, new in slabs_for(cur, x, J, y, ranges):
            status[y] = (kind, j); rec(i + 1, cur + new, status)
        status.pop(y, None)
    rec(0, cons, {})
def root():
    cons = []
    cons.append(Con(vec([(1, 1), (0, -1)]), True))                 # rho_2 > rho_1 = 1
    for i in range(1, 6): cons.append(Con(vec([(i + 1, 1), (i, -1)]), True))
    cons.append(Con(vec([(0, RHOMAX), (6, -1)]), False))             # rho_7 <= RHOMAX  (RHOMAX*rho_1 - rho_7 >= 0)
    return cons
# ---- exact cascade for soundness / coverage
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
def exact_sig(rhos):
    steps, Rend = path(rhos); return tuple((mv["setter"] + 1, mv["lap"]) for mv in steps)
if __name__ == "__main__":
    t0 = time.time()
    cons0 = root()
    expand(cons0, 0, 0, [], 0)
    print("window rho_7 <= %d: nodes %d, leaves (cells) %d, deepest path %d, %.0fs" % (RHOMAX, nodes, len(leaves), deepest, time.time() - t0))
    cut = [l for l in leaves if l[0] == "DEPTH"]; print("branches cut at depth 40:", len(cut))
    good = [l for l in leaves if l[0] == "LEAF"]
    sigs = {}
    for _, path_, cons, _st in good: sigs.setdefault(tuple(path_), []).append(cons)
    print("distinct results (path signatures):", len(sigs))
    # soundness: exact witness of each cell
    bad = 0; nowit = 0
    for sig, cl in sigs.items():
        for cons in cl:
            ok, v = feasible(cons)
            w = None
            for den in (10**3, 10**4, 10**6, 10**8):
                cand = [F(x).limit_denominator(den) for x in v]
                if all(k.exact(cand) for k in cons): w = cand; break
            if w is None: nowit += 1; continue
            rhos = [F(1)] + w
            if exact_sig(rhos) != sig: bad += 1
    print("cells without an exact rational witness:", nowit, "; cells whose exact cascade path differs from the cell's path:", bad)
    # coverage: random arrangements
    rnd = random.Random(322); miss = multi = 0; N = 4000; per = {}
    allcells = [(sig, cons) for sig, cl in sigs.items() for cons in cl]
    for _ in range(N):
        xs = sorted(F(rnd.randint(1000, RHOMAX * 1000), 1000) for _ in range(6))
        if len(set(xs)) < 6 or xs[0] <= 1: continue
        hits = [sig for sig, cons in allcells if all(k.exact(xs) for k in cons)]
        s = exact_sig([F(1)] + xs)
        if not hits: miss += 1
        elif len(hits) > 1: multi += 1
        elif hits[0] != s: miss += 1
    print("coverage on %d random arrangements: in no cell (or the wrong cell): %d, in more than one cell: %d" % (N, miss, multi))
    import pickle; pickle.dump([(sig, [(k.ec, k.ec0, k.strict) for k in cons]) for sig, cons in allcells], open("symbolic_cells_J%d.pkl" % J_W, "wb"))
