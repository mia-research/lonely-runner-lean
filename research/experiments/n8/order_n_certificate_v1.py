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
    m = len(A); nv = len(c)
    art = [i for i in range(m) if b[i] < 0]
    ncol = nv + m + len(art)
    T = [[F(0)] * (ncol + 1) for _ in range(m)]
    basis = [0] * m
    ai = nv + m
    for i in range(m):
        s = -1 if b[i] < 0 else 1
        for j in range(nv): T[i][j] = F(s) * A[i][j]
        T[i][nv + i] = F(s)
        T[i][ncol] = F(s) * b[i]
        if s < 0:
            T[i][ai] = F(1); basis[i] = ai; ai += 1
        else:
            basis[i] = nv + i
    cost = [(F(0), F(x)) for x in c] + [(F(0), F(0))] * m + [(F(1), F(0))] * len(art)
    while True:
        cB = [cost[bi] for bi in basis]
        enter = -1
        for j in range(ncol):
            if j in basis: continue
            rc0 = cost[j][0] - sum(cB[i][0] * T[i][j] for i in range(m))
            rc1 = cost[j][1] - sum(cB[i][1] * T[i][j] for i in range(m))
            if _lt((rc0, rc1), NEG): enter = j; break
        if enter < 0: break
        leave = -1; best = None
        for i in range(m):
            if T[i][enter] > 0:
                r = T[i][ncol] / T[i][enter]
                if best is None or r < best or (r == best and basis[i] < basis[leave]):
                    best = r; leave = i
        if leave < 0: return 'unbounded'
        pv = T[leave][enter]
        T[leave] = [x / pv for x in T[leave]]
        for i in range(m):
            if i != leave and T[i][enter] != 0:
                f = T[i][enter]; T[i] = [a - f * bb for a, bb in zip(T[i], T[leave])]
        basis[leave] = enter
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
def extend(word, S, L, best, stats):
    cons = constraints(word)
    stats[0] += 1
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
            extend(word + [(nx, nq)], S, L, best, stats)
def job(args):
    S, L, first = args
    best = [None, None, None]; stats = [0, 0]
    extend([first], S, L, best, stats)
    return best, stats
if __name__ == '__main__':
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    L = (CAP * S - 1) // n
    starts = [(x, q) for x in range(1, NV + 1) for q in range(1, L + 1)]
    print(f'order {n} certificate (strict, simplex): ratio bound S = {S}, lap bound L = {L}, words to {NV*L} moves, cap R < {CAP}')
    import time
    t0 = time.time(); res = []
    with Pool() as pool:
        for i, r in enumerate(pool.imap_unordered(job, [(S, L, s) for s in starts]), 1):
            res.append(r)
            b, st = r
            cur = max((x[0][0] for x in res if x[0][0] is not None), default=None)
            print(f'   [{i}/{len(starts)}] {time.time()-t0:7.1f}s  nodes {sum(y[0] for _, y in res)}'
                  f'  realisable {sum(y[1] for _, y in res)}  best so far {cur}', flush=True)
    cand = [b for b, _ in res if b[0] is not None]
    nodes = sum(s[0] for _, s in res); feas = sum(s[1] for _, s in res)
    print(f'   words tested: {nodes}   realisable (max tau > 0): {feas}')
    if cand:
        best = max(cand, key=lambda b: b[0])
        print(f'   largest sup R over realisable words: {best[0]} = {float(best[0]):.4f}   word {best[1]}   margin tau = {best[2]}')
        print(f'   target sup R < 4  ->  {"PROVED for ratio <= " + str(S) if best[0] < 4 else "NOT proved"}')
    else:
        print('   no realisable word -- cascade cannot move at this ratio bound')
