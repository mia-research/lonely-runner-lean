"""modgap_tree_v1 (2026-10-06): the path tree of the arc criterion, adapted from path_tree_v3 (same symbolic cascade: branch on the setter and the straddlers; a node's region is [state lonely] U its children).
Object: six readings 0 < r <= rho_0 < ... < rho_5 <= RMAX (ratios to d_min), the 1/7-cascade of the six readings in u = 7*m*t started at u = 1; a state is (x, J) with u = (7J+1)/rho_x, the start is x = 6 (rho_6 = 1), J = 0.
Zones of reading y: ((7j-1)/rho_y, (7j+1)/rho_y).  A child (w, j): u lies in w's zone j, and no reading y has a zone j' with start < u and end > the new exit (ties to the larger index).  The child splits by its exit: > 6 (a FAIL cell: the arc criterion
fails) or <= 6 (continues).  A node has no FAIL descendant exactly when the arc criterion holds on its cell.  Feasibility of a cell: LP with a slack on the strict inequalities (floats steer; every FAIL cell's witness is rationalised and run through the exact cascade).
[PROVISIONAL: covering; supports: whether a FAIL cell exists in the window r <= rho_i <= RMAX, a statement about the cells of that window and not an existence claim]  [TREE if the run completes with no cut node]."""
import sys, time, os
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
R0 = F(sys.argv[1]); RMAX = F(sys.argv[2]); DMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 80
TAG = sys.argv[4] if len(sys.argv) > 4 else 'x'
NV = 7                     # rho_0..rho_5 and rho_6 = 1
TT = 1e-9
BOUNDS = [(float(R0), float(RMAX))] * 6 + [(1.0, 1.0)]
class Con:
    __slots__ = ("c", "strict", "ec", "norm")
    def __init__(self, a, strict):
        self.ec = [F(x) for x in a]; self.c = np.array([float(x) for x in a]); self.strict = strict
        self.norm = float(np.linalg.norm(self.c)) or 1.0
def vec(pairs):
    a = [F(0)] * NV
    for i, c in pairs: a[i] += F(c)
    return a
def feasible(cons):
    A = []; b = []
    for k in cons:
        A.append(list(-k.c) + [k.norm if k.strict else 0.0]); b.append(0.0)
    res = linprog([0.0] * NV + [-1.0], A_ub=np.array(A), b_ub=np.array(b), bounds=BOUNDS + [(0, 1)], method="highs")
    if res.status != 0: return False, None
    if any(k.strict for k in cons) and res.x[-1] < TT: return False, None
    return True, res.x[:NV]
def rng(cons, i):
    A = [list(-k.c) for k in cons]; b = [0.0] * len(cons); out = []
    for sg in (1, -1):
        cb = [0.0] * NV; cb[i] = sg
        res = linprog(cb, A_ub=np.array(A), b_ub=np.array(b), bounds=BOUNDS, method="highs")
        out.append(res.x[i] if res.status == 0 else None)
    return out[0], out[1]
nodes = 0; maxdepth = 0; fails = []; cut = []; t0 = time.time()
def expand(cons, x, J, path, depth):
    global nodes, maxdepth
    nodes += 1; maxdepth = max(maxdepth, depth)
    if nodes % 200 == 0: print("   nodes %d, depth %d, fail %d, cut %d, %.0fs" % (nodes, maxdepth, len(fails), len(cut), time.time() - t0), file=sys.stderr, flush=True)
    if depth >= DMAX: cut.append(path); return
    ranges = [rng(cons, y) for y in range(NV)]
    for w in range(6):
        if w == x: continue
        lo_w, hi_w = ranges[w]; lo_x, hi_x = ranges[x]
        pmin = (7 * J + 1) * lo_w / hi_x; pmax = (7 * J + 1) * hi_w / lo_x          # = u * rho_w
        for j in range(max(1, int((pmin - 1) // 7)), int((pmax + 1) // 7) + 2):
            zone = [Con(vec([(w, 7 * J + 1), (x, -(7 * j - 1))]), True), Con(vec([(x, 7 * j + 1), (w, -(7 * J + 1))]), True)]
            base = cons + zone
            ok, _ = feasible(base)
            if not ok: continue
            pend = []
            ranges2 = [rng(base, y) for y in range(NV)]
            for y in range(6):
                if y == w or y == x: continue
                lo_y, hi_y = ranges2[y]; lo_x2, hi_x2 = ranges2[x]
                qmin = (7 * J + 1) * lo_y / hi_x2; qmax = (7 * J + 1) * hi_y / lo_x2
                for jp in range(max(1, int((qmin - 1) // 7)), int((qmax + 1) // 7) + 2):
                    s1 = Con(vec([(y, 7 * J + 1), (x, -(7 * jp - 1))]), True)                                  # zone start < u
                    s2 = Con(vec([(w, 7 * jp + 1), (y, -(7 * j + 1))]), y < w)                                 # zone end > exit (ties: y > w wins)
                    ok2, _ = feasible(base + [s1, s2])
                    if ok2: pend.append((y, jp, s1, s2))
            def rec(i, cur):
                if i == len(pend):
                    ok3, _ = feasible(cur)
                    if not ok3: return
                    # split by the exit: fail if (7j+1) > 6 rho_w
                    failc = Con(vec([(6, 7 * j + 1), (w, -6)]), True)       # (7j+1) - 6 rho_w > 0   (rho_6 = 1 carries the constant)
                    contc = Con(vec([(w, 6), (6, -(7 * j + 1))]), False)    # 6 rho_w - (7j+1) >= 0
                    okf, pt = feasible(cur + [failc])
                    if okf: fails.append((path + [(w, j)], cur + [failc], pt))
                    okc, _ = feasible(cur + [contc])
                    if okc: expand(cur + [contc], w, j, path + [(w, j)], depth + 1)
                    return
                y, jp, s1, s2 = pend[i]
                A = Con(vec([(x, 7 * jp - 1), (y, -(7 * J + 1))]), False)           # start >= u
                okA, _ = feasible(cur + [A])
                if okA: rec(i + 1, cur + [A])
                negs2 = Con(vec([(y, 7 * j + 1), (w, -(7 * jp + 1))]), y > w)       # end <= exit (strict for y > w)
                okB, _ = feasible(cur + [s1, negs2])
                if okB: rec(i + 1, cur + [s1, negs2])
            rec(0, base)
def root():
    cons = [Con(vec([(i + 1, 1), (i, -1)]), True) for i in range(5)]                  # rho_0 < ... < rho_5
    return cons
def exact_check(pt):
    rho = sorted(F(v).limit_denominator(10**5) for v in pt[:6]); u = F(1)
    if rho[0] < R0 or rho[-1] > RMAX: return None
    for _ in range(4000):
        bl = []
        for q in rho:
            xx = q * u / 7; N = round(xx)
            if abs(xx - N) < F(1, 7): bl.append(F(7 * N + 1) / q)
        if not bl: return (u <= 6, u, rho)
        u = max(bl)
        if u > 6: return (False, u, rho)
    return None
if __name__ == "__main__":
    out = open('modgap_tree_v1_%s.out' % TAG, 'w'); out.write(__doc__ + "\n")
    def log(s): out.write(s + "\n"); out.flush(); print(s, flush=True)
    log("window: R0 = %s, RMAX = %s, DMAX = %d" % (R0, RMAX, DMAX))
    expand(root(), 6, 0, [], 0)
    log("DONE: nodes %d, deepest %d, FAIL cells %d, cut nodes %d, %.0fs" % (nodes, maxdepth, len(fails), len(cut), time.time() - t0))
    for p, c, pt in fails[:20]:
        ec = exact_check(pt)
        log("FAIL cell path %s ; witness %s ; exact cascade: %s" % (p, [round(float(v), 4) for v in pt[:6]], (ec[0], str(ec[1])) if ec else None))
    out.close()
