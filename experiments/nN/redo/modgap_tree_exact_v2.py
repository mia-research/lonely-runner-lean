"""modgap_tree_exact_v2 (2026-10-06): modgap_tree_exact_v1 with a parameter ARCS (environment variable, 1 or 2).
ARCS = 1 is v1 unchanged in its branching (the arc criterion A: the six readings' 1/7-cascade from u = 1 lands at most 6).
ARCS = 2 runs the cascade of the full seven readings S = {d_min} + six at threshold 1/7 in u = 7 d_min t from u = 1:
d_min (index 6, rho_6 = 1) is a reading like the others, with zones (7j - 1, 7j + 1) in u, so it is in the way on (6, 8),
(13, 15), ...; its clear arcs are [7k - 6, 7k - 1] [P].  A FAIL cell is a path whose last exit exceeds 13: S's own 1/7
landing is beyond d_min's second arc [8, 13].  The statement A2 tested: S is lonely at 1/7 at an instant of d_min's first or
second clear arc (u <= 13), the place where E419 found the twelve exact counterexamples of A isolated (via d_min's own exit
u = 8) and where modgap_arc_index_v1 finds every 1/7-lonely A-failure on [1, 44] (1,538 of 1,538).
Every other statement, certificate and grade is v1's: a branch is pruned only with a verified exact Motzkin certificate,
zone enumerations are closed by certificates, and a FAIL cell counts only with an exact witness whose exact cascade (of
the six for ARCS = 1, of all seven for ARCS = 2) lands beyond the arc end.
[PROVISIONAL: covering; supports: the arc statement on the window R0 <= rho_i <= RMAX, a statement about the cells of that
window; for ARCS = 2 it is an existence statement at 1/7 for those arrangements, with the landing's place named]
Usage: ARCS=2 python3 modgap_tree_exact_v2.py R0 RMAX TAG [R0_FIRST_MAX]
"""
import sys, time, os, itertools
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
import multiprocessing as mp

NV = 7
R0 = F(sys.argv[1]) if len(sys.argv) > 1 else F(36, 5)
RMAX = F(sys.argv[2]) if len(sys.argv) > 2 else F(16)
TAG = sys.argv[3] if len(sys.argv) > 3 else 'x'
R0MAX = F(sys.argv[4]) if len(sys.argv) > 4 else None
DMAX = 80
TT = 1e-7
ARCS = int(os.environ.get('ARCS', '1'))
UEND = 6 if ARCS == 1 else 13
NR = 6 if ARCS == 1 else 7      # readings that can block: the six, or the six and d_min


def vec(pairs):
    a = [F(0)] * NV
    for i, c in pairs:
        a[i] += F(c)
    return tuple(a)


class Con:
    __slots__ = ('a', 'strict', 'f')

    def __init__(self, a, strict):
        self.a = tuple(F(x) for x in a); self.strict = strict
        self.f = np.array([float(x) for x in self.a])


def box():
    cs = []
    for i in range(6):
        cs.append(Con(vec([(i, 1), (6, -R0)]), False))
        cs.append(Con(vec([(6, RMAX), (i, -1)]), False))
    if R0MAX is not None:
        cs.append(Con(vec([(6, R0MAX), (0, -1)]), False))
    return cs


BOX = None

# ---------------------------------------------------------------- exact linear algebra


def exact_solve_nonneg(cols, target, order):
    """Find y >= 0 (Fractions) with sum_k y_k cols[k] = target.  Columns tried in `order` (float weights, largest first);
    a basic solution on an independent subset; None if that fails."""
    m = len(target)
    chosen = []; rowsM = []
    # build basis greedily by exact elimination
    basis_cols = []
    R = []           # reduced rows for independence test: we keep an echelon form of chosen columns
    piv = []
    def reduce_col(v):
        v = list(v)
        for (r, pc, pv) in R:
            if v[pc] != 0:
                fct = v[pc] / pv
                v = [vi - fct * ri for vi, ri in zip(v, r)]
        return v
    for k in order:
        v = reduce_col(cols[k])
        nz = next((i for i in range(m) if v[i] != 0), None)
        if nz is None:
            continue
        R.append((v, nz, v[nz])); basis_cols.append(k)
        if len(basis_cols) == m:
            break
    # solve sum_{k in basis} y_k cols[k] = target exactly (least: system may be overdetermined; check consistency)
    nb = len(basis_cols)
    Mx = [[cols[k][i] for k in basis_cols] + [target[i]] for i in range(m)]
    # Gaussian elimination
    r = 0; pivcols = []
    for c in range(nb):
        p = next((i for i in range(r, m) if Mx[i][c] != 0), None)
        if p is None:
            continue
        Mx[r], Mx[p] = Mx[p], Mx[r]
        pv = Mx[r][c]
        Mx[r] = [v / pv for v in Mx[r]]
        for i in range(m):
            if i != r and Mx[i][c] != 0:
                fct = Mx[i][c]
                Mx[i] = [vi - fct * ri for vi, ri in zip(Mx[i], Mx[r])]
        pivcols.append(c); r += 1
        if r == m:
            break
    for i in range(r, m):
        if Mx[i][nb] != 0:
            return None
    y = [F(0)] * nb
    for i, c in enumerate(pivcols):
        y[c] = Mx[i][nb]
    if any(v < 0 for v in y):
        return None
    out = {}
    for c, k in enumerate(basis_cols):
        if y[c] != 0:
            out[k] = y[c]
    return out


def exact_phase1(cols, target):
    """Exact simplex, phase 1: y >= 0 with sum y_k cols[k] = target.  Bland's rule.  Returns dict or None."""
    m = len(target); n = len(cols)
    # make target >= 0
    sign = [1 if t >= 0 else -1 for t in target]
    T = []
    for i in range(m):
        T.append([sign[i] * cols[k][i] for k in range(n)] + [F(1) if j == i else F(0) for j in range(m)] + [sign[i] * target[i]])
    basis = [n + i for i in range(m)]
    W = n + m
    # objective: minimise sum of artificials  -> reduced costs
    def obj_row():
        z = [F(0)] * (W + 1)
        for j in range(n, n + m):
            z[j] = F(1)
        for i in range(m):
            if basis[i] >= n:
                Ti = T[i]
                for j in range(W + 1):
                    z[j] -= Ti[j]
        return z
    for _ in range(5000):
        z = obj_row()
        ent = next((j for j in range(W) if z[j] < 0 and j not in basis), None)
        if ent is None:
            break
        rows = [(T[i][W] / T[i][ent], basis[i], i) for i in range(m) if T[i][ent] > 0]
        if not rows:
            return None
        _, _, piv = min(rows)
        pv = T[piv][ent]
        T[piv] = [v / pv for v in T[piv]]
        for i in range(m):
            if i != piv and T[i][ent] != 0:
                fct = T[i][ent]
                T[i] = [vi - fct * ri for vi, ri in zip(T[i], T[piv])]
        basis[piv] = ent
    if any(basis[i] >= n and T[i][W] != 0 for i in range(m)):
        return None
    out = {}
    for i in range(m):
        if basis[i] < n and T[i][W] != 0:
            out[basis[i]] = T[i][W]
    return out


def verify_motzkin(cons, y):
    """sum y_k a_k = 0 over all 7 coordinates (row rho_6 > 0 = index len(cons), vector e_6), strict weight = 1, y >= 0."""
    tot = [F(0)] * NV; sw = F(0)
    for k, v in y.items():
        if v < 0:
            return False
        if k == len(cons):
            tot[6] += v; sw += v
        else:
            a = cons[k].a
            for i in range(NV):
                tot[i] += v * a[i]
            if cons[k].strict:
                sw += v
    return all(t == 0 for t in tot) and sw == 1


STATS = {'lp': 0, 'cert_direct': 0, 'cert_phase1': 0, 'cert_fail': 0}


def decide(cons):
    """('empty', None) with a verified exact certificate, or ('open', float point) otherwise."""
    STATS['lp'] += 1
    nrow = len(cons)
    A = np.zeros((nrow + 3, NV + 1)); b = np.zeros(nrow + 3)
    for k, c in enumerate(cons):
        A[k, :NV] = -c.f
        if c.strict:
            A[k, NV] = 1.0
    A[nrow, 6] = -1.0; A[nrow, NV] = 1.0                       # rho_6 > 0
    A[nrow + 1, 6] = 1.0; b[nrow + 1] = 1.0                   # rho_6 <= 1
    A[nrow + 2, NV] = 1.0; b[nrow + 2] = 1.0                  # s <= 1
    cvec = np.zeros(NV + 1); cvec[NV] = -1.0
    res = linprog(cvec, A_ub=A, b_ub=b, bounds=[(None, None)] * (NV + 1), method='highs')
    if res.status == 0 and -res.fun > TT:
        x = res.x
        return 'open', x[:NV] / x[6]
    # try an exact certificate
    if res.status == 0:
        yf = -res.ineqlin.marginals
    else:
        yf = np.ones(nrow + 3)
    cand = [k for k in range(nrow + 1) if yf[k] > 1e-13]
    cols = {}
    def col(k):
        if k == nrow:
            return tuple([F(0)] * 6 + [F(-1)] + [F(1)])
        c = cons[k]
        return tuple([-v for v in c.a] + [F(1) if c.strict else F(0)])
    target = tuple([F(0)] * NV + [F(1)])
    allcols = {k: col(k) for k in range(nrow + 1)}
    order = sorted(cand, key=lambda k: -yf[k])
    y = exact_solve_nonneg(allcols, target, order)
    if y is not None and verify_motzkin(cons, y):
        STATS['cert_direct'] += 1
        return 'empty', None
    keys = list(range(nrow + 1))
    y2 = exact_phase1([allcols[k] for k in keys], list(target))
    if y2 is not None:
        y2 = {keys[k]: v for k, v in y2.items()}
        if verify_motzkin(cons, y2):
            STATS['cert_phase1'] += 1
            return 'empty', None
    STATS['cert_fail'] += 1
    x = res.x if res.status == 0 else None
    return 'open', (x[:NV] / x[6] if x is not None and x[6] > 0 else None)


def frange(cons, i):
    A = np.array([-c.f for c in cons]); b = np.zeros(len(cons)); out = []
    for sg in (1, -1):
        cb = np.zeros(NV); cb[i] = sg
        bnds = [(None, None)] * 6 + [(1.0, 1.0)]
        res = linprog(cb, A_ub=A, b_ub=b, bounds=bnds, method='highs')
        out.append(res.x[i] if res.status == 0 else None)
    return out


def exact_point_in(cons, pt):
    if pt is None:
        return None
    for den in (10 ** 4, 10 ** 6, 10 ** 9, 10 ** 12, 10 ** 15):
        r = [F(float(v)).limit_denominator(den) for v in pt[:6]] + [F(1)]
        ok = True
        for c in cons:
            val = sum(ai * ri for ai, ri in zip(c.a, r))
            if (c.strict and val <= 0) or (not c.strict and val < 0):
                ok = False; break
        if ok:
            return r
    return None


def exact_cascade(rho):
    if ARCS == 2:
        rho = list(rho) + [F(1)]
    u = F(1)
    for _ in range(10000):
        bl = []
        for q in rho:
            xx = q * u / 7; N = round(xx)
            if abs(xx - N) < F(1, 7):
                bl.append(F(7 * N + 1) / q)
        if not bl:
            return u
        u = max(bl)
        if u > UEND:
            return u
    return None


def tail_ok(cons, extra):
    st, _ = decide(cons + [extra])
    return st == 'empty'


def jrange_w(cons, ranges, x, J, w):
    """Zones j of w that can contain u = (7J+1)/rho_x, with certified tails: below, emptiness of
    (7J+1) rho_w < (7 jlo - 6) rho_x; above, emptiness of (7J+1) rho_w > (7 jhi + 6) rho_x."""
    lo_w, hi_w = ranges[w]; lo_x, hi_x = ranges[x]
    if None in (lo_w, hi_w, lo_x, hi_x):
        lo_w, hi_w = float(R0), float(RMAX)
        lo_x, hi_x = (1.0, 1.0) if x == 6 else (float(R0), float(RMAX))
    pmin = (7 * J + 1) * lo_w / hi_x; pmax = (7 * J + 1) * hi_w / lo_x
    jlo = max(1, int((pmin - 1) // 7)); jhi = int((pmax + 1) // 7) + 1
    while jlo > 1:
        if tail_ok(cons, Con(vec([(x, 7 * jlo - 6), (w, -(7 * J + 1))]), True)):
            break
        jlo -= 1
    while not tail_ok(cons, Con(vec([(w, 7 * J + 1), (x, -(7 * jhi + 6))]), True)):
        jhi += 1
    return range(jlo, jhi + 1)


def jrange_y(cons, ranges, x, J, w, j, y):
    """Straddler zones jp of y at state (x, J) against setter (w, j), with certified tails:
    below: zones jp < jlo have end (7jp+1)/rho_y <= exit_w, certified by emptiness of (7jlo - 6) rho_w > (7j+1) rho_y;
    above: zones jp > jhi have start (7jp-1)/rho_y >= u, certified by emptiness of (7J+1) rho_y > (7jhi + 6) rho_x."""
    lo_y, hi_y = ranges[y]; lo_x, hi_x = ranges[x]
    if None in (lo_y, hi_y, lo_x, hi_x):
        lo_y, hi_y = float(R0), float(RMAX)
        lo_x, hi_x = (1.0, 1.0) if x == 6 else (float(R0), float(RMAX))
    qmin = (7 * J + 1) * lo_y / hi_x; qmax = (7 * J + 1) * hi_y / lo_x
    jlo = max(1, int((qmin - 1) // 7)); jhi = int((qmax + 1) // 7) + 1
    while jlo > 1:
        extra = Con(vec([(w, 7 * jlo - 6), (y, -(7 * j + 1))]), y < w)     # end of zone jlo-1 >= / > exit (tie rule)
        if tail_ok(cons, extra):
            break
        jlo -= 1
    while True:
        extra = Con(vec([(y, 7 * J + 1), (x, -(7 * jhi + 6))]), True)
        if tail_ok(cons, extra):
            break
        jhi += 1
    return range(jlo, jhi + 1)


def sup_rho0(cell):
    """sup of rho_0 (= rho_min) over the closure of a FAIL cell intersected with rho_i <= RMAX, with the box lower bounds
    and the slab bound dropped.  Exact: dual multipliers y >= 0 (Fractions) with sum y_k (-a_k[:6]) = e_0 give
    rho_0 <= sum y_k a_k[6] on the closed cell; a primal point of the closed cell attaining it, solved exactly on the dual
    support and checked against every row.  Returns (bound, primal_ok, rmax_in_support, point) or None."""
    nb = 12 + (1 if R0MAX is not None else 0)
    rows = [a for a, st in cell[nb:]]
    for i in range(6):
        rows.append(vec([(6, RMAX), (i, -1)]))          # rho_i <= RMAX
        rows.append(vec([(i, 1)]))                      # rho_i >= 0
    tags = ['cell'] * (len(cell) - nb) + sum([['rmax', 'nonneg'] for i in range(6)], [])
    Af = np.array([[-float(a[i]) for i in range(6)] for a in rows]); bf = np.array([float(a[6]) for a in rows])
    c = np.zeros(6); c[0] = -1.0
    res = linprog(c, A_ub=Af, b_ub=bf, bounds=[(None, None)] * 6, method='highs')
    if res.status != 0:
        return None
    yf = -res.ineqlin.marginals
    order = sorted([k for k in range(len(rows)) if yf[k] > 1e-11], key=lambda k: -yf[k])
    cols = {k: tuple(-rows[k][i] for i in range(6)) for k in range(len(rows))}
    target = tuple(F(1) if i == 0 else F(0) for i in range(6))
    y = exact_solve_nonneg(cols, target, order)
    if y is None:
        y = exact_phase1([cols[k] for k in range(len(rows))], list(target))
        if y is None:
            return None
    chk = [sum(v * cols[k][i] for k, v in y.items()) for i in range(6)]
    if chk != list(target) or any(v < 0 for v in y.values()):
        return None
    bound = sum(v * rows[k][6] for k, v in y.items())
    # primal: support rows tight, rho_0 = bound; free coordinates fixed at the float optimum
    sup = list(y.keys())
    eqs = [([-rows[k][i] for i in range(6)], rows[k][6]) for k in sup] + [([F(1)] + [F(0)] * 5, bound)]
    pt = None
    # exact elimination with free variables set to the rationalised float optimum
    m = len(eqs); M = [list(a) + [b] for a, b in eqs]
    r = 0; pivc = []
    for cidx in range(6):
        pr = next((i for i in range(r, m) if M[i][cidx] != 0), None)
        if pr is None: continue
        M[r], M[pr] = M[pr], M[r]; pv = M[r][cidx]; M[r] = [v / pv for v in M[r]]
        for i in range(m):
            if i != r and M[i][cidx] != 0:
                fct = M[i][cidx]; M[i] = [vi - fct * ri for vi, ri in zip(M[i], M[r])]
        pivc.append(cidx); r += 1
    consistent = all(M[i][6] == 0 for i in range(r, m))
    if consistent:
        free = [cidx for cidx in range(6) if cidx not in pivc]
        xv = [None] * 6
        for cidx in free:
            xv[cidx] = F(float(res.x[cidx])).limit_denominator(10 ** 6)
        for i, cidx in enumerate(pivc):
            xv[cidx] = M[i][6] - sum(M[i][f] * xv[f] for f in free)
        pt = xv + [F(1)]
    ok = pt is not None and all(sum(a[i] * pt[i] for i in range(7)) >= 0 for a in rows)
    return bound, ok, any(tags[k] == 'rmax' for k in sup), ([str(v) for v in pt[:6]] if pt else None)


def root():
    return box() + [Con(vec([(i + 1, 1), (i, -1)]), True) for i in range(5)]


def run_task(task):
    cons_spec, x, J, path, depth = task
    cons = [Con(a, s) for a, s in cons_spec]
    out = {'nodes': 0, 'maxdepth': 0, 'cut': [], 'pruned': 0, 'fail': [], 'unresolved': [], 'failcells': []}
    for k in STATS:
        STATS[k] = 0
    expand(cons, x, J, path, depth, out)
    out['stats'] = dict(STATS)
    return out


# --- splitting: run the root's first step serially and hand out its continue-children
SPLIT = []


def expand(cons, x, J, path, depth, out, split_depth=None):
    """The tree below the state (x, J) with cell cons.  With split_depth, children at that depth are recorded as tasks."""
    if split_depth is not None and depth == split_depth:
        SPLIT.append(([(c.a, c.strict) for c in cons], x, J, path, depth)); return
    out['nodes'] += 1
    out['maxdepth'] = max(out['maxdepth'], depth)
    if depth >= DMAX:
        out['cut'].append(path); return
    ranges = [frange(cons, y) for y in range(NV)]
    for w in range(NR):
        if w == x:
            continue
        for j in jrange_w(cons, ranges, x, J, w):
            zone = [Con(vec([(w, 7 * J + 1), (x, -(7 * j - 1))]), True), Con(vec([(x, 7 * j + 1), (w, -(7 * J + 1))]), True)]
            base = cons + zone
            st, _ = decide(base)
            if st == 'empty':
                out['pruned'] += 1; continue
            ranges2 = [frange(base, y) for y in range(NV)]
            pend = []
            for y in range(NR):
                if y == w or y == x:
                    continue
                for jp in jrange_y(base, ranges2, x, J, w, j, y):
                    s1 = Con(vec([(y, 7 * J + 1), (x, -(7 * jp - 1))]), True)
                    s2 = Con(vec([(w, 7 * jp + 1), (y, -(7 * j + 1))]), y < w)
                    st2, _ = decide(base + [s1, s2])
                    if st2 == 'empty':
                        out['pruned'] += 1; continue
                    pend.append((y, jp, s1, s2))

            def rec(i, cur):
                if i == len(pend):
                    st3, _ = decide(cur)
                    if st3 == 'empty':
                        out['pruned'] += 1; return
                    failc = Con(vec([(6, 7 * j + 1), (w, -UEND)]), True)
                    contc = Con(vec([(w, UEND), (6, -(7 * j + 1))]), False)
                    stf, ptf = decide(cur + [failc])
                    if stf == 'empty':
                        out['pruned'] += 1
                    else:
                        r = exact_point_in(cur + [failc], ptf)
                        if r is not None:
                            land = exact_cascade(sorted(r[:6]))
                            if land is not None and land > UEND:
                                out['fail'].append((path + [(w, j)], [str(v) for v in r[:6]], str(land)))
                                out['failcells'].append([(c.a, c.strict) for c in cur + [failc]])
                            else:
                                out['unresolved'].append((path + [(w, j)], 'witness point does not fail', [str(v) for v in r[:6]]))
                        else:
                            out['unresolved'].append((path + [(w, j)], 'no exact point', None))
                    stc, _ = decide(cur + [contc])
                    if stc == 'empty':
                        out['pruned'] += 1
                    else:
                        expand(cur + [contc], w, j, path + [(w, j)], depth + 1, out, split_depth)
                    return
                y, jp, s1, s2 = pend[i]
                Acon = Con(vec([(x, 7 * jp - 1), (y, -(7 * J + 1))]), False)
                stA, _ = decide(cur + [Acon])
                if stA == 'empty':
                    out['pruned'] += 1
                else:
                    rec(i + 1, cur + [Acon])
                negs2 = Con(vec([(y, 7 * j + 1), (w, -(7 * jp + 1))]), y > w)
                stB, _ = decide(cur + [s1, negs2])
                if stB == 'empty':
                    out['pruned'] += 1
                else:
                    rec(i + 1, cur + [s1, negs2])
            rec(0, base)


if __name__ == '__main__':
    t0 = time.time()
    out = open('modgap_tree_exact_v2_%s.out' % TAG, 'w'); out.write(__doc__ + "\n")
    def log(s):
        out.write(s + "\n"); out.flush(); print(s, flush=True)
    log("window: R0 = %s, RMAX = %s, rho_0 <= %s, DMAX = %d, ARCS = %d (landing must be <= %d)" % (R0, RMAX, R0MAX, DMAX, ARCS, UEND))
    head = {'nodes': 0, 'maxdepth': 0, 'cut': [], 'pruned': 0, 'fail': [], 'unresolved': [], 'failcells': []}
    SPLIT_DEPTH = int(os.environ.get('SPLIT_DEPTH', '2'))
    expand(root(), 6, 0, [], 0, head, SPLIT_DEPTH)
    log("head (depth < %d): nodes %d, pruned %d, FAIL %d, unresolved %d; tasks %d; %.0fs" %
        (SPLIT_DEPTH, head['nodes'], head['pruned'], len(head['fail']), len(head['unresolved']), len(SPLIT), time.time() - t0))
    head_stats = dict(STATS)
    tot = dict(head); tot['cut'] = list(head['cut']); tot['fail'] = list(head['fail']); tot['unresolved'] = list(head['unresolved'])
    tot['failcells'] = list(head['failcells'])
    stats = dict(head_stats)
    nproc = int(os.environ.get('NPROC', '9'))
    done = 0
    with mp.get_context('fork').Pool(nproc) as pool:
        for r in pool.imap_unordered(run_task, SPLIT):
            done += 1
            tot['nodes'] += r['nodes']; tot['pruned'] += r['pruned']; tot['maxdepth'] = max(tot['maxdepth'], r['maxdepth'])
            tot['cut'] += r['cut']; tot['fail'] += r['fail']; tot['unresolved'] += r['unresolved']; tot['failcells'] += r['failcells']
            for k, v in r['stats'].items():
                stats[k] = stats.get(k, 0) + v
            if done % 10 == 0 or done == len(SPLIT):
                log("  tasks %d/%d: nodes %d, pruned %d, FAIL %d, unresolved %d, cut %d, certificates direct %d phase1 %d failed %d, %.0fs" %
                    (done, len(SPLIT), tot['nodes'], tot['pruned'], len(tot['fail']), len(tot['unresolved']), len(tot['cut']),
                     stats['cert_direct'], stats['cert_phase1'], stats['cert_fail'], time.time() - t0))
    log("DONE: nodes %d, deepest %d, pruned (each with a verified exact certificate) %d, FAIL cells with exact witnesses %d, "
        "UNRESOLVED candidates %d, cut nodes %d; LPs %d; certificates: direct %d, phase-1 %d, not found (branch explored) %d; %.0fs" %
        (tot['nodes'], tot['maxdepth'], tot['pruned'], len(tot['fail']), len(tot['unresolved']), len(tot['cut']), stats['lp'],
         stats['cert_direct'], stats['cert_phase1'], stats['cert_fail'], time.time() - t0))
    for f in tot['fail'][:40]:
        log("FAIL path %s ; exact witness rho %s ; exact landing %s" % f)
    best = None
    for idx, cell in enumerate(tot['failcells']):
        sr = sup_rho0(cell)
        log("FAIL cell %d: sup of rho_min over its closure (rho_i <= RMAX, no lower bounds): %s ; primal point attains it: %s ; "
            "RMAX in the dual support: %s ; point %s" % (idx, sr[0] if sr else None, sr[1] if sr else None, sr[2] if sr else None, sr[3] if sr else None))
        if sr and (best is None or sr[0] > best):
            best = sr[0]
    log("max over the FAIL cells of the certified sup of rho_min: %s" % best)
    for f in tot['unresolved'][:40]:
        log("UNRESOLVED %s" % (f,))
    verdict = ('EXACT: no FAIL cell, no unresolved candidate, no cut node: the arc statement holds on the whole window [TREE, every prune an exact certificate]'
               if not tot['fail'] and not tot['unresolved'] and not tot['cut'] else
               'not a proof for the window: see FAIL / UNRESOLVED / cut above')
    log("verdict: %s" % verdict)
    out.close()
