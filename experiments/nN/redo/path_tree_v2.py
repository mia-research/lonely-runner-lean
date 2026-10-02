# PATH TREE over polyhedral cells (v2).  Same symbolic cascade as symbolic_cells_v1, but the tree branches on the SETTER and on possible STRADDLERS only.
# State definer (x, J): R = (8J+1)/rho_x (start: x = reading 1, J = 0, R = 1).  Next setter (w, j): R lies in its zone ((8j-1)/rho_w, (8j+1)/rho_w); the
# new state is its exit R' = (8j+1)/rho_w.  Exactness of the max: no other reading y has a zone (y, j') with start < R and end > R' (a straddler); ties
# go to the larger index.  A non-setter blocker whose end is <= R' does not change the path, so it is NOT split off.
# Node = (cell, path).  Children = all feasible setters.  A node's region splits as  [R lonely]  U  children  (cascade semantics).
# Tree finite  <=>  every arrangement of the window lands.  Nodes at depth > DMAX are reported (unresolved).
import sys, time, random
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
J_W = int(sys.argv[1]) if len(sys.argv) > 1 else 1
DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 60
RHOMAX = 8 * J_W + 1
exec(open('symbolic_cells_v1.py').read().split("nodes = 0; leaves = []")[0].split("J_W = int(sys.argv[1]) if len(sys.argv) > 1 else 1\nRHOMAX = 8 * J_W + 1\n")[1])
def u_range(ranges, x, J, y):
    lo_y, hi_y = ranges[y]; lo_x, hi_x = ranges[x]
    return (8 * J + 1) * lo_y / hi_x, (8 * J + 1) * hi_y / lo_x
nodes = 0; maxdepth = 0; cut = []; term = []; t0 = time.time(); lonely_nodes = 0
def expand(cons, x, J, path, depth):
    global nodes, maxdepth, lonely_nodes
    nodes += 1; maxdepth = max(maxdepth, depth)
    if nodes % 500 == 0: print("   nodes %d, depth %d, terminal %d, cut %d, %.0fs" % (nodes, maxdepth, len(term), len(cut), time.time() - t0), file=sys.stderr, flush=True)
    if depth >= DMAX: cut.append((path, cons)); return
    ranges = {y: rho_range(cons, y) for y in range(7)}
    nchild = 0
    for w in range(7):
        if w == x: continue
        umin, umax = u_range(ranges, x, J, w)
        for j in range(max(1, int((umin - 1) // 8)), int((umax + 1) // 8) + 2):
            chain = [Con(vec([(w, 8 * J + 1), (x, -(8 * j - 1))]), True), Con(vec([(x, 8 * j + 1), (w, -(8 * J + 1))]), True)]
            ok, _ = feasible(cons + chain)
            if not ok: continue
            # straddlers: for each y != w, x and each lap j' with sigma_{y,j'} < R and eps_{y,j'} > R'
            base = cons + chain
            pend = []
            ranges2 = {y: rho_range(base, y) for y in range(7)}
            for y in range(7):
                if y == w or y == x: continue
                umin_y, umax_y = u_range(ranges2, x, J, y)
                for jp in range(max(1, int((umin_y - 1) // 8)), int((umax_y + 1) // 8) + 2):
                    # straddle region: (8jp-1) rho_x < (8J+1) rho_y   and   (8jp+1) rho_w > (8j+1) rho_y   (ties: y>w must have eps_y < eps_w, so eps_y >= eps_w is a straddle for y > w)
                    s1 = Con(vec([(y, 8 * J + 1), (x, -(8 * jp - 1))]), True)
                    s2 = Con(vec([(w, 8 * jp + 1), (y, -(8 * j + 1))]), y < w)     # y<w: eps_y > eps_w strict straddles ; y>w: eps_y >= eps_w straddles
                    ok2, _ = feasible(base + [s1, s2])
                    if ok2: pend.append((y, jp, s1, s2))
            # exclude every feasible straddle: for each pending (y,jp): either sigma >= R (non-strict) or eps <= R' (the opposite of s2)
            def rec(i, cur):
                if i == len(pend):
                    ok3, _ = feasible(cur)
                    if ok3:
                        nonlocal_nchild[0] += 1; expand(cur, w, j, path + [(w + 1, j)], depth + 1)
                    return
                y, jp, s1, s2 = pend[i]
                A = Con(vec([(x, 8 * jp - 1), (y, -(8 * J + 1))]), False)                       # sigma >= R : (8jp-1) rho_x >= (8J+1) rho_y
                okA, _ = feasible(cur + [A])
                if okA: rec(i + 1, cur + [A])
                # B: sigma < R (strict, s1) and NOT s2   (eps <= R' for y<w ; eps < R' for y>w)
                if y < w: negs2 = Con(vec([(y, 8 * j + 1), (w, -(8 * jp + 1))]), False)      # eps_y <= eps_w : (8j+1)... 
                else: negs2 = Con(vec([(y, 8 * j + 1), (w, -(8 * jp + 1))]), True)
                # eps_y = (8jp+1)/rho_y ; eps_w = (8j+1)/rho_w ; eps_y <= eps_w  <=>  (8jp+1) rho_w <= (8j+1) rho_y
                negs2 = Con(vec([(y, 8 * j + 1), (w, -(8 * jp + 1))]), y > w)
                okB, _ = feasible(cur + [s1, negs2])
                if okB: rec(i + 1, cur + [s1, negs2])
            nonlocal_nchild = [0]
            rec(0, base)
            nchild += nonlocal_nchild[0]
    if nchild == 0: term.append((path, cons))
def root():
    cons = [Con(vec([(1, 1), (0, -1)]), True)]
    for i in range(1, 6): cons.append(Con(vec([(i + 1, 1), (i, -1)]), True))
    cons.append(Con(vec([(0, RHOMAX), (6, -1)]), False)); return cons
if __name__ == "__main__":
    c0 = root(); expand(c0, 0, 0, [], 0)
    print("window rho_7 <= %d: nodes %d, deepest %d, terminal nodes %d, nodes cut at depth %d: %d, %.0fs" % (RHOMAX, nodes, maxdepth, len(term), DMAX, len(cut), time.time() - t0))
    import pickle; pickle.dump(([(p, [(k.ec, k.ec0, k.strict) for k in c]) for p, c in term], [(p, [(k.ec, k.ec0, k.strict) for k in c]) for p, c in cut]), open("path_tree_J%d.pkl" % J_W, "wb"))
