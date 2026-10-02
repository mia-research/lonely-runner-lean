# Check the path tree (path_tree_v3 pickle) against the exact cascade:
#  (1) partition: for random exact arrangements in the window and for LP witnesses of random nodes, walk the tree; at each node the arrangement lies in exactly one child
#      (and that child's setter equals the exact cascade's setter) or in none, in which case the exact cascade must land there (no blocker);
#  (2) soundness of cells: an exact rational witness of each sampled node reproduces the node's path as the prefix of its exact path.
import sys, pickle, random, time
from fractions import Fraction as F
J_W = int(sys.argv[1]) if len(sys.argv) > 1 else 1
RHOMAX = 8 * J_W + 1
exec(open('symbolic_cells_v1.py').read().split("nodes = 0; leaves = []")[0].split("J_W = int(sys.argv[1]) if len(sys.argv) > 1 else 1\nRHOMAX = 8 * J_W + 1\n")[1])
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
ALL = pickle.load(open("path_tree3_J%d_all.pkl" % J_W, "rb"))
print("tree nodes:", len(ALL), "; deepest path:", max(len(n[1]) for n in ALL))
kids = {}
for i, (par, p, cs, df) in enumerate(ALL): kids.setdefault(par, []).append(i)
def inside(node, v):
    for ec, ec0, strict in ALL[node][2]:
        s = ec0 + sum(c * x for c, x in zip(ec, v))
        if (s <= 0) if strict else (s < 0): return False
    return True
def walk(rhos):                      # rhos = [1] + v (sorted exactly)
    v = rhos[1:]; node = 0; steps, Rend = path(rhos)
    for i, mv in enumerate(steps):
        c = [k for k in kids.get(node, []) if inside(k, v)]
        if len(c) != 1: return ("children containing the arrangement: %d at depth %d" % (len(c), i), None)
        if ALL[c[0]][1][-1] != (mv["setter"] + 1, mv["lap"]): return ("setter mismatch at depth %d: tree %s cascade %s" % (i, ALL[c[0]][1][-1], (mv["setter"] + 1, mv["lap"])), None)
        node = c[0]
    c = [k for k in kids.get(node, []) if inside(k, v)]
    if c: return ("lands but a child contains it", None)
    return (None, len(steps))
rnd = random.Random(326); bad = 0; tot = 0; depths = {}
t0 = time.time()
for _ in range(3000):
    xs = sorted(F(rnd.randint(1001, RHOMAX * 1000), 1000) for _ in range(6))
    if len(set(xs)) < 6: continue
    r, d = walk([F(1)] + xs); tot += 1
    if r: bad += 1; print("   violation:", r, [float(x) for x in xs]) if bad < 6 else None
    else: depths[d] = depths.get(d, 0) + 1
print("random arrangements: %d, violations %d, path lengths seen %s (%.0fs)" % (tot, bad, sorted(depths.items())[:12], time.time() - t0))
# witnesses of random nodes (deep ones included)
nodes_ = list(range(len(ALL))); rnd.shuffle(nodes_); bad2 = nowit = ok2 = 0
for nd in nodes_[:1500]:
    cons = [Con([F(0)] + list(ec), strict) if False else None for ec, ec0, strict in ALL[nd][2]]
    cons = []
    for ec, ec0, strict in ALL[nd][2]:
        k = Con([ec0] + [F(0)] * 0 + [F(x) for x in ec], strict)    # Con takes a = [a_1..a_7]: a_1 constant, a_2..a_7 coefficients
        cons.append(k)
    okf, v = feasible(cons)
    if not okf: nowit += 1; continue
    w = None
    for den in (10**3, 10**4, 10**6, 10**8):
        cand = [F(x).limit_denominator(den) for x in v]
        if all(k.exact(cand) for k in cons): w = cand; break
    if w is None: nowit += 1; continue
    r, d = walk([F(1)] + w)
    pre = ALL[nd][1]; steps, Rend = path([F(1)] + w); got = [(mv["setter"] + 1, mv["lap"]) for mv in steps][:len(pre)]
    if r or got != pre: bad2 += 1; print("   node witness mismatch:", r, pre, got) if bad2 < 6 else None
    else: ok2 += 1
print("node witnesses: %d checked ok, %d without an exact witness, %d mismatches" % (ok2, nowit, bad2))
