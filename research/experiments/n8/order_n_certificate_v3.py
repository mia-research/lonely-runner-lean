"""Order-n finite certificate, exact rational simplex. Generalises order5_certificate_v3.py to any order.

v2 solved each LP by enumerating every 4-subset of the constraint rows: at depth 18 that is C(60,4) ~ 4.9e5 exact
4x4 solves per call, which does not finish at ratio 8. This version solves the identical LP with a two-phase
(big-M) primal simplex in exact Fraction arithmetic and Bland's rule, so the answers are exact, not numerical.

Unknowns (u2, u3, u4, tau), u_i in [1, S], tau in [0, 1]. Every "in the way" and "the instant advances"
condition is tightened by tau:  a.u + tau <= b.
Step 1: maximise tau. If max tau <= 0 the word is not realisable with strict inequalities -- discard it.
Step 2: on the closed polyhedron (tau = 0), minimise the last setter's reading; sup R = (5Q+1)/min u.

Why the two steps compose (margin realisability). The feasible set is convex and tau is one of its coordinates,
so if any point has tau > 0 then every tau = 0 feasible point is a limit of tau > 0 feasible points (slide along
the segment to the positive-margin witness). Hence inf u over the closed polyhedron equals inf u over the open
(strictly realisable) region, and sup R over realisable configurations is exactly (5Q+1)/(min u) -- a supremum,
not attained. The margin threshold and the R-supremum are therefore proved jointly, not sequentially.
"""
import itertools, sys
from fractions import Fraction as F
from multiprocessing import Pool
n = int(__import__('os').environ.get('ORDER', 5)); th = F(1, n); NV = n - 2   # readings u_2..u_{n-1}
CAP = n - 1

# ---------------------------------------------------------------- exact simplex
# minimise c.x subject to A x <= b, x >= 0, in exact rationals.
# Rows with b_i < 0 are negated and carry an artificial variable priced at M (costs are (M_coeff, const) pairs
# compared lexicographically).  Bland's rule: no cycling.
NEG = (0, 0)
def _lt(p, q): return p[0] < q[0] or (p[0] == q[0] and p[1] < q[1])
def simplex_min(A, b, c):
    """Exact two-phase (big-M) primal simplex, Bland's rule. Costs are (M_coeff, const) pairs.

    The reduced-cost row is carried IN the tableau and updated in O(ncol) per pivot, instead of
    being recomputed as O(m*ncol) from the basis each iteration; membership in the basis is a flag
    array rather than a list scan. Same arithmetic, same pivots, same answers -- just not repeated.
    """
    m = len(A); nv = len(c)
    art = [i for i in range(m) if b[i] < 0]
    ncol = nv + m + len(art)
    T = [[F(0)] * (ncol + 1) for _ in range(m)]
    basis = [0] * m
    inbasis = [False] * ncol
    ai = nv + m
    for i in range(m):
        s = -1 if b[i] < 0 else 1
        Ai = A[i]; Ti = T[i]
        for j in range(nv): Ti[j] = F(s) * Ai[j]
        Ti[nv + i] = F(s)
        Ti[ncol] = F(s) * b[i]
        if s < 0:
            Ti[ai] = F(1); basis[i] = ai; ai += 1
        else:
            basis[i] = nv + i
        inbasis[basis[i]] = True
    cost = [(F(0), F(x)) for x in c] + [(F(0), F(0))] * m + [(F(1), F(0))] * len(art)
    # reduced-cost rows, computed once: rc[j] = cost[j] - sum_i cB[i] * T[i][j]
    rc0 = [F(0)] * (ncol + 1); rc1 = [F(0)] * (ncol + 1)
    for j in range(ncol + 1):
        s0 = F(0); s1 = F(0)
        for i in range(m):
            t = T[i][j]
            if t:
                cb = cost[basis[i]]
                if cb[0]: s0 += cb[0] * t
                if cb[1]: s1 += cb[1] * t
        if j < ncol:
            rc0[j] = cost[j][0] - s0; rc1[j] = cost[j][1] - s1
        else:
            rc0[j] = -s0; rc1[j] = -s1
    while True:
        enter = -1
        for j in range(ncol):
            if inbasis[j]: continue
            a = rc0[j]
            if a < 0 or (a == 0 and rc1[j] < 0): enter = j; break
        if enter < 0: break
        leave = -1; best = None
        for i in range(m):
            tie = T[i][enter]
            if tie > 0:
                r = T[i][ncol] / tie
                if best is None or r < best or (r == best and basis[i] < basis[leave]):
                    best = r; leave = i
        if leave < 0: return 'unbounded'
        pv = T[leave][enter]
        Tl = [x / pv for x in T[leave]]; T[leave] = Tl
        for i in range(m):
            if i != leave:
                f = T[i][enter]
                if f: T[i] = [a - f * bb for a, bb in zip(T[i], Tl)]
        f0 = rc0[enter]; f1 = rc1[enter]
        if f0: rc0 = [a - f0 * bb for a, bb in zip(rc0, Tl)]
        if f1: rc1 = [a - f1 * bb for a, bb in zip(rc1, Tl)]
        inbasis[basis[leave]] = False; basis[leave] = enter; inbasis[enter] = True
    if any(basis[i] >= nv + m and T[i][ncol] != 0 for i in range(m)): return None   # infeasible
    x = [F(0)] * nv
    for i in range(m):
        if basis[i] < nv: x[basis[i]] = T[i][ncol]
    return sum(ci * xi for ci, xi in zip(c, x)), x

def opt(cons, obj, sense, S, with_tau):
    """cons: (a2,a3,a4,at,b) meaning a.u + at*tau <= b.  obj: 0..2 = u index, 3 = tau.
    Shift u_i = 1 + y_i (y_i >= 0, y_i <= S-1); tau = t >= 0, t <= 1 (dropped when with_tau is False)."""
    nv = NV + 1 if with_tau else NV
    A = []; b = []
    for c in cons:
        row = list(c[:NV]) + ([c[NV]] if with_tau else [])
        A.append(row); b.append(c[NV + 1] - sum(c[:NV]))
    for i in range(NV):
        e = [F(0)] * nv; e[i] = F(1); A.append(e); b.append(F(S - 1))
    if with_tau:
        e = [F(0)] * nv; e[NV] = F(1); A.append(e); b.append(F(1))
    c = [F(0)] * nv
    c[obj] = F(-1) if sense == 'max' else F(1)
    r = simplex_min(A, b, c)
    if r is None or r == 'unbounded': return None
    v = r[1][obj]
    return v + 1 if obj < NV else v          # undo the u shift
# ---------------------------------------------------------------- word LPs (identical to v2)
def coeff(idx, val):
    v = [F(0)] * NV; c = F(0)
    if idx == 0: c = val
    else: v[idx - 1] = val
    return v, c
def constraints(word):
    cons = []
    def add(a, at, bb): cons.append(tuple(a) + (at, bb))
    x1, Q1 = word[0]
    v, c = coeff(x1, th)
    add(v, F(1), F(Q1) + th - c); add([-t for t in v], F(1), -(F(Q1) - th) + c)
    for j in range(1, len(word)):
        xp, Qp = word[j - 1]; xj, Qj = word[j]
        vj, cj = coeff(xj, F(Qp) + th); vp, cp = coeff(xp, F(Qj)); vs, cs = coeff(xp, th)
        add([vj[i] - vp[i] - vs[i] for i in range(NV)], F(1), cs + cp - cj)
        add([-(vj[i] - vp[i]) - vs[i] for i in range(NV)], F(1), cs - cp + cj)
        vA, cA = coeff(xp, F(Qj) + th); vB, cB = coeff(xj, F(Qp) + th)
        add([vB[i] - vA[i] for i in range(NV)], F(1), cA - cB)
    return cons
class Budget(Exception):
    """Raised inside a worker when its node budget is exhausted. Never raised when NODE_BUDGET = 0."""

def extend(word, S, L, best, stats, budget):
    cons = constraints(word)
    stats[0] += 1
    if budget and stats[0] > budget: raise Budget
    tau = opt(cons, NV, 'max', S, True)
    if tau is None or tau <= 0: return
    stats[1] += 1
    x, Q = word[-1]
    m = opt(cons, x - 1, 'min', S, False) if x > 0 else F(1)
    if m is not None and m > 0:
        R = F(n * Q + 1) / m
        if best[0] is None or R > best[0]: best[0] = R; best[1] = list(word); best[2] = tau
    if len(word) >= NV * L: return
    used = {xx: QQ for xx, QQ in word}
    for nx in range(1, NV + 1):
        for nq in range(used.get(nx, 0) + 1, L + 1):
            extend(word + [(nx, nq)], S, L, best, stats, budget)

def _worker_init():
    """Kill this worker if the parent dies abruptly.

    multiprocessing marks Pool workers daemon=True, but that is enforced by the PARENT's atexit
    handler (multiprocessing.util._exit_function), not by the OS. A parent killed with SIGKILL --
    or a closed terminal session -- runs no atexit handler, so the workers survive, are reparented
    to launchd (ppid 1), and spin forever on a result pipe nobody will ever read. Six such orphans
    burned 44 CPU-hours on 2026-09-16/17. This watchdog closes that hole.
    """
    import threading, os, time as _t
    def watch():
        while True:
            if os.getppid() == 1: os._exit(1)
            _t.sleep(2)
    threading.Thread(target=watch, daemon=True).start()

def job(args):
    S, L, first, budget = args
    best = [None, None, None]; stats = [0, 0]; truncated = False
    try:
        extend([first], S, L, best, stats, budget)
    except Budget:
        truncated = True
    return first, best, stats, truncated

if __name__ == '__main__':
    import os, signal, threading, time
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    L = (CAP * S - 1) // n
    BUDGET = int(os.environ.get('NODE_BUDGET', 0))    # 0 = unlimited = identical maths to v1/v2
    HB = float(os.environ.get('HEARTBEAT', 60))       # seconds between outstanding-work reports
    starts = [(x, q) for x in range(1, NV + 1) for q in range(1, L + 1)]
    print(f'order {n} certificate (strict, simplex): ratio bound S = {S}, lap bound L = {L}, words to {NV*L} moves, cap R < {CAP}')
    print(f'   node budget per start: {BUDGET if BUDGET else "unlimited"}   heartbeat: {HB:g}s   workers: {os.cpu_count()}')

    t0 = time.time(); res = []
    done = set(); lock = threading.Lock(); stop_hb = threading.Event()
    def heartbeat():
        while not stop_hb.wait(HB):
            with lock: d = set(done)
            out = [s for s in starts if s not in d]
            print(f'   .. {time.time()-t0:7.1f}s  {len(d)}/{len(starts)} done   still running: '
                  f'{out[:8]}{" +%d more" % (len(out)-8) if len(out) > 8 else ""}', flush=True)
    threading.Thread(target=heartbeat, daemon=True).start()

    pool = None
    def _bail(signum, frame):
        # SIGTERM default-kills the parent without running the `with` block's __exit__, which is
        # exactly how the orphans were created. Terminate the pool explicitly, then exit.
        print(f'\n   !! signal {signum} -- terminating pool', flush=True)
        stop_hb.set()
        if pool is not None: pool.terminate()
        sys.exit(128 + signum)
    signal.signal(signal.SIGTERM, _bail)
    signal.signal(signal.SIGINT, _bail)

    with Pool(initializer=_worker_init) as pool:
        for i, r in enumerate(pool.imap_unordered(job, [(S, L, s, BUDGET) for s in starts]), 1):
            res.append(r)
            first, b, st, trunc = r
            with lock: done.add(first)
            cur = max((x[1][0] for x in res if x[1][0] is not None), default=None)
            print(f'   [{i}/{len(starts)}] {time.time()-t0:7.1f}s  start {first}'
                  f'  nodes {sum(y[0] for _, _, y, _ in res)}'
                  f'  realisable {sum(y[1] for _, _, y, _ in res)}'
                  f'  best so far {cur}{"  [TRUNCATED]" if trunc else ""}', flush=True)
    stop_hb.set()

    cut = [f for f, _, _, t in res if t]
    cand = [b for _, b, _, _ in res if b[0] is not None]
    nodes = sum(s[0] for _, _, s, _ in res); feas = sum(s[1] for _, _, s, _ in res)
    print(f'   words tested: {nodes}   realisable (max tau > 0): {feas}')

    # ---- claim integrity -------------------------------------------------------------------
    # A truncated start leaves words unexamined, so its `best` is only a LOWER bound on that
    # start's sup R. That is fatal to a PROVED verdict (an unexamined word could exceed 4) and
    # fatal to "no realisable word" (an unexamined word could be realisable). It is NOT fatal to
    # a refutation: a witness with R >= 4 stands on its own regardless of what was skipped.
    if cut:
        print(f'   !! INCOMPLETE: {len(cut)}/{len(starts)} starts hit the node budget: {cut}')
        print(f'   !! sup R below is a LOWER BOUND only. Re-run with NODE_BUDGET=0 to certify.')
    if cand:
        best = max(cand, key=lambda b: b[0])
        print(f'   largest sup R over realisable words: {best[0]} = {float(best[0]):.4f}   word {best[1]}   margin tau = {best[2]}')
        if best[0] >= 4:
            print(f'   target sup R < 4  ->  NOT proved (witness attains {float(best[0]):.4f})')
        elif cut:
            print(f'   target sup R < 4  ->  NOT PROVED -- search incomplete, verdict withheld')
        else:
            print(f'   target sup R < 4  ->  PROVED for ratio <= {S}')
    elif cut:
        print('   no realisable word FOUND, but the search was incomplete -- no conclusion')
    else:
        print('   no realisable word -- cascade cannot move at this ratio bound')
