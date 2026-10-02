# PATH TREE, parallel, with built-in checks.  Window rho_7 <= 8J+1.  Splits the first levels serially, solves the subtrees in a process pool.
# Per node: LP range of the definer's reading gives the exact supremum of the state R = (8J+1)/rho_x over the cell (closure); the max over all nodes is the
# supremum of the landing R* over the window.  Partition check: a fixed list of exact test arrangements (random + the hardest known) is carried down the tree;
# at each node every test arrangement in the cell lies in at most one child, and if in none the exact cascade lands there; every node's path is the prefix of its
# exact path.  Violations are reported with the arrangement.
import sys, time, random, pickle
from fractions import Fraction as F
from multiprocessing import Pool
import os
TT = float(os.environ.get("TT", "1e-9"))
import numpy as np
from scipy.optimize import linprog
J_W = int(sys.argv[1]) if len(sys.argv) > 1 else 1
DMAX = 60
RHOMAX = 8 * J_W + 1
exec(open('path_tree_v2.py').read().split("nodes = 0; maxdepth = 0")[0].split("DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 60\nRHOMAX = 8 * J_W + 1\n")[1])
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
def root():
    cons = [Con(vec([(1, 1), (0, -1)]), True)]
    for i in range(1, 6): cons.append(Con(vec([(i + 1, 1), (i, -1)]), True))
    cons.append(Con(vec([(0, RHOMAX), (6, -1)]), False)); return cons
def make_tests(n=250, seed=327):
    rnd = random.Random(seed); tests = []
    while len(tests) < n:
        xs = sorted(F(rnd.randint(1001, RHOMAX * 1000), 1000) for _ in range(6))
        if len(set(xs)) == 6: tests.append(xs)
    hard = [[2.3664, 3.149, 4.1961, 5.2243, 5.7986, 7.4502], [2.3089, 3.2365, 4.2023, 5.2324, 5.8113, 7.4612], [2.3594, 3.3086, 4.3152, 5.3594, 5.9672, 7.6617],
            [2.3865, 3.2428, 4.2747, 5.313, 5.9875, 7.6003], [2.5181, 3.1987, 4.1343, 4.5189, 5.6212, 7.0187], [2.4802, 3.3741, 4.4674, 5.5535, 6.1772, 7.9347]]
    for h in hard: tests.append([F(x).limit_denominator(10**6) for x in h])
    return tests
TESTS = make_tests()
EXACT = {}
def exact_path_of(i):
    if i not in EXACT:
        steps, Rend = path([F(1)] + TESTS[i]); EXACT[i] = [(mv["setter"] + 1, mv["lap"]) for mv in steps]
    return EXACT[i]
def member(cons, v):
    return all(k.exact(v) for k in cons)
THR = (3, 5, 7, 9, 10, 11, 11.5)
class Stats:
    def __init__(s): s.terms = []; s.nodes = 0; s.term = 0; s.maxdepth = 0; s.supR = 0.0; s.supat = None; s.viol = []; s.cut = 0; s.lonelyhere = 0; s.hi7 = {t: 0.0 for t in THR}
def expand2(cons, x, J, path_, depth, active, st):
    st.nodes += 1; st.maxdepth = max(st.maxdepth, depth)
    if depth >= DMAX: st.cut += 1; return
    ranges = {y: rho_range(cons, y) for y in range(7)}
    lo_x = ranges[x][0]; Rb = (8 * J + 1) / lo_x
    if Rb > st.supR: st.supR = Rb; st.supat = (list(path_), Rb)
    for t in THR:
        if Rb > t and ranges[6][1] > st.hi7[t]: st.hi7[t] = ranges[6][1]
    # test arrangements: soundness of the prefix
    for i in active:
        ep = exact_path_of(i)
        if ep[:len(path_)] != path_: st.viol.append(("prefix", i, path_, ep[:len(path_) + 1]))
    claimed = {i: 0 for i in active}
    nchild = 0
    for w in range(7):
        if w == x: continue
        umin, umax = u_range(ranges, x, J, w)
        for j in range(max(1, int((umin - 1) // 8)), int((umax + 1) // 8) + 2):
            chain = [Con(vec([(w, 8 * J + 1), (x, -(8 * j - 1))]), True), Con(vec([(x, 8 * j + 1), (w, -(8 * J + 1))]), True)]
            ok, _ = feasible(cons + chain)
            if not ok: continue
            base = cons + chain; pend = []
            ranges2 = {y: rho_range(base, y) for y in range(7)}
            for y in range(7):
                if y == w or y == x: continue
                umin_y, umax_y = u_range(ranges2, x, J, y)
                for jp in range(max(1, int((umin_y - 1) // 8)), int((umax_y + 1) // 8) + 2):
                    s1 = Con(vec([(y, 8 * J + 1), (x, -(8 * jp - 1))]), True)
                    s2 = Con(vec([(w, 8 * jp + 1), (y, -(8 * j + 1))]), y < w)
                    ok2, _ = feasible(base + [s1, s2])
                    if ok2: pend.append((y, jp, s1, s2))
            cnt = [0]
            def rec(i, cur):
                if i == len(pend):
                    ok3, _ = feasible(cur)
                    if ok3:
                        cnt[0] += 1
                        sub = [a for a in active if member(cur[len(cons):], TESTS[a])]
                        for a in sub: claimed[a] += 1
                        expand2(cur, w, j, path_ + [(w + 1, j)], depth + 1, sub, st)
                    return
                y, jp, s1, s2 = pend[i]
                A = Con(vec([(x, 8 * jp - 1), (y, -(8 * J + 1))]), False)
                okA, _ = feasible(cur + [A])
                if okA: rec(i + 1, cur + [A])
                negs2 = Con(vec([(y, 8 * j + 1), (w, -(8 * jp + 1))]), y > w)
                okB, _ = feasible(cur + [s1, negs2])
                if okB: rec(i + 1, cur + [s1, negs2])
            rec(0, base); nchild += cnt[0]
    if nchild == 0:
        st.term += 1; _ok, _w = feasible(cons); st.terms.append((tuple(path_), (8 * J + 1) / ranges[x][1], (8 * J + 1) / ranges[x][0], [tuple(ranges[y]) for y in range(7)], None if _w is None else [float(v) for v in _w], [(tuple(k.ec), k.ec0, k.strict) for k in cons]))
    for a in active:
        ep = exact_path_of(a)
        if claimed[a] > 1: st.viol.append(("in several children", a, path_))
        if claimed[a] == 0 and len(ep) != len(path_): st.viol.append(("in no child but the exact path continues", a, path_, ep))
SHORT = []; FRONT_NODES = [0]
def frontier(root_cons, levels=2):
    """serially expand the first levels, returning node specs"""
    specs = [(root_cons, 0, 0, [], 0, list(range(len(TESTS))))]
    for _ in range(levels):
        nxt = []
        for cons, x, J, p, d, act in specs:
            n0 = len(nxt); FRONT_NODES[0] += 1
            ranges = {y: rho_range(cons, y) for y in range(7)}
            for w in range(7):
                if w == x: continue
                umin, umax = u_range(ranges, x, J, w)
                for j in range(max(1, int((umin - 1) // 8)), int((umax + 1) // 8) + 2):
                    chain = [Con(vec([(w, 8 * J + 1), (x, -(8 * j - 1))]), True), Con(vec([(x, 8 * j + 1), (w, -(8 * J + 1))]), True)]
                    ok, _ = feasible(cons + chain)
                    if not ok: continue
                    base = cons + chain; pend = []
                    ranges2 = {y: rho_range(base, y) for y in range(7)}
                    for y in range(7):
                        if y == w or y == x: continue
                        umin_y, umax_y = u_range(ranges2, x, J, y)
                        for jp in range(max(1, int((umin_y - 1) // 8)), int((umax_y + 1) // 8) + 2):
                            s1 = Con(vec([(y, 8 * J + 1), (x, -(8 * jp - 1))]), True); s2 = Con(vec([(w, 8 * jp + 1), (y, -(8 * j + 1))]), y < w)
                            ok2, _ = feasible(base + [s1, s2])
                            if ok2: pend.append((y, jp, s1, s2))
                    def rec(i, cur):
                        if i == len(pend):
                            ok3, _ = feasible(cur)
                            if ok3: nxt.append((cur, w, j, p + [(w + 1, j)], d + 1, [a for a in act if member(cur[len(cons):], TESTS[a])]))
                            return
                        y, jp, s1, s2 = pend[i]
                        A = Con(vec([(x, 8 * jp - 1), (y, -(8 * J + 1))]), False)
                        okA, _ = feasible(cur + [A])
                        if okA: rec(i + 1, cur + [A])
                        negs2 = Con(vec([(y, 8 * j + 1), (w, -(8 * jp + 1))]), y > w)
                        okB, _ = feasible(cur + [s1, negs2])
                        if okB: rec(i + 1, cur + [s1, negs2])
                    rec(0, base)
            if len(nxt) == n0:
                _ok, _w = feasible(cons); SHORT.append((tuple(p), (8 * J + 1) / ranges[x][1], (8 * J + 1) / ranges[x][0], [tuple(ranges[y]) for y in range(7)], None if _w is None else [float(v) for v in _w], [(tuple(k.ec), k.ec0, k.strict) for k in cons]))
        specs = nxt
    return specs
def work(spec):
    cons, x, J, p, d, act = spec; st = Stats(); t = time.time()
    expand2(cons, x, J, p, d, act, st)
    return (p, st.nodes, st.term, st.maxdepth, st.supR, st.supat, st.viol[:5], st.cut, time.time() - t, st.hi7, st.terms)
if __name__ == "__main__":
    t0 = time.time(); specs = frontier(root(), levels=int(sys.argv[2]) if len(sys.argv) > 2 else 2)
    print("window rho_7 <= %d: frontier of %d subtrees (depth %d), %.0fs" % (RHOMAX, len(specs), specs[0][4] if specs else 0, time.time() - t0), flush=True)
    tot = Stats(); ALLTERMS = list(SHORT); tot.nodes += FRONT_NODES[0]; tot.term += len(SHORT); _cnt = [0]
    print('frontier nodes', FRONT_NODES[0], 'shallow terminals', len(SHORT), flush=True)
    with Pool(int(sys.argv[3]) if len(sys.argv) > 3 else 9) as pool:
        for r in pool.imap_unordered(work, specs):
            p, n, tm, md, sR, sat, viol, cut, sec, hi7, terms = r
            ALLTERMS.extend(terms); _cnt[0] += 1
            if _cnt[0] % 500 == 0: pickle.dump(ALLTERMS, open('terminals6_J%d.partial.pkl' % J_W, 'wb'))
            for t in THR: tot.hi7[t] = max(tot.hi7[t], hi7[t])
            tot.nodes += n; tot.term += tm; tot.maxdepth = max(tot.maxdepth, md); tot.cut += cut; tot.viol += viol
            if sR > tot.supR: tot.supR = sR; tot.supat = sat
            print("   subtree %-24s nodes %6d terminal %5d depth %2d sup R %.4f violations %d (%.0fs)  | total nodes %d, sup R so far %.4f" % (p, n, tm, md, sR, len(viol), sec, tot.nodes, tot.supR), flush=True)
    import pickle; pickle.dump(ALLTERMS, open("terminals6_J%d.pkl" % J_W, "wb"))
    print("LATE LANDINGS: largest rho_7 (closure) among nodes whose state can exceed T:", {t: round(tot.hi7[t], 4) for t in THR}, flush=True)
    print("DONE window rho_7 <= %d: nodes %d, terminal %d, deepest %d, nodes cut at depth %d: %d, SUPREMUM of the landing R* over the window = %.6f at path %s, violations of the partition/soundness checks: %d, %.0fs" % (
        RHOMAX, tot.nodes, tot.term, tot.maxdepth, DMAX, tot.cut, tot.supR, tot.supat, len(tot.viol), time.time() - t0), flush=True)
    for v in tot.viol[:10]: print("   violation:", v)
