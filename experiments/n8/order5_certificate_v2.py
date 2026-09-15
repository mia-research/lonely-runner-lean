"""Order 5 finite certificate with the boundary discipline enforced (v1 without it returned the known 4.125 artefact: an
all-boundary word that BSM counts clear).

Unknowns (u2, u3, u4, tau). Every "in the way" and "the instant advances" condition is tightened by tau:
    a.u + tau <= b        (so tau > 0 means the word is realisable with strict inequalities)
Step 1: maximise tau. If max tau <= 0 the word is not realisable — discard it.
Step 2: on the closed polyhedron (tau = 0), minimise the last setter's reading; sup R = (5Q+1)/min u.
Exact rational vertex enumeration in four variables."""
import itertools, sys
from fractions import Fraction as F
from multiprocessing import Pool
n = 5; th = F(1, n)
def solve(rows):
    m = [list(r) for r in rows]; d = len(m)
    for i in range(d):
        p = next((r for r in range(i, d) if m[r][i] != 0), None)
        if p is None: return None
        m[i], m[p] = m[p], m[i]
        pv = m[i][i]
        m[i] = [x / pv for x in m[i]]
        for r in range(d):
            if r != i and m[r][i] != 0:
                f = m[r][i]; m[r] = [a - f * b for a, b in zip(m[r], m[i])]
    return [m[i][d] for i in range(d)]
def opt(cons, obj, sense, S):
    """cons: (a2,a3,a4,at,b) meaning a.u + at*tau <= b. obj: index 0..3 (3 = tau). sense: 'min'/'max'."""
    A = list(cons)
    for i in range(3):
        e = [F(0)]*4; e[i] = F(-1); A.append(tuple(e) + (F(-1),))
        e = [F(0)]*4; e[i] = F(1);  A.append(tuple(e) + (F(S),))
    e = [F(0)]*4; e[3] = F(-1); A.append(tuple(e) + (F(0),))      # tau >= 0
    e = [F(0)]*4; e[3] = F(1);  A.append(tuple(e) + (F(1),))      # tau <= 1
    best = None
    for tri in itertools.combinations(A, 4):
        rows = [[c[0], c[1], c[2], c[3], c[4]] for c in tri]
        p = solve(rows)
        if p is None: continue
        if any(sum(a * x for a, x in zip(c[:4], p)) > c[4] for c in A): continue
        v = p[obj]
        if best is None or (v < best if sense == 'min' else v > best): best = v
    return best
def coeff(idx, val):
    v = [F(0)]*3; c = F(0)
    if idx == 0: c = val
    else: v[idx-1] = val
    return v, c
def constraints(word):
    cons = []
    def add(a, at, b): cons.append((a[0], a[1], a[2], at, b))
    x1, Q1 = word[0]
    v, c = coeff(x1, F(1, 5))
    add(v, F(1), F(Q1) + th - c); add([-t for t in v], F(1), -(F(Q1) - th) + c)
    for j in range(1, len(word)):
        xp, Qp = word[j-1]; xj, Qj = word[j]
        vj, cj = coeff(xj, F(Qp) + th); vp, cp = coeff(xp, F(Qj)); vs, cs = coeff(xp, th)
        add([vj[i] - vp[i] - vs[i] for i in range(3)], F(1), cs + cp - cj)
        add([-(vj[i] - vp[i]) - vs[i] for i in range(3)], F(1), cs - cp + cj)
        vA, cA = coeff(xp, F(Qj) + th); vB, cB = coeff(xj, F(Qp) + th)
        add([vB[i] - vA[i] for i in range(3)], F(1), cA - cB)
    return cons
def extend(word, S, L, best):
    cons = constraints(word)
    tau = opt(cons, 3, 'max', S)
    if tau is None or tau <= 0: return                      # not realisable with strict inequalities
    x, Q = word[-1]
    m = opt(cons, x - 1, 'min', S) if x > 0 else F(1)
    if m is not None and m > 0:
        R = F(5 * Q + 1) / m
        if best[0] is None or R > best[0]: best[0] = R; best[1] = list(word); best[2] = tau
    if len(word) >= 3 * L: return
    used = {xx: QQ for xx, QQ in word}
    for nx in (1, 2, 3):
        for nq in range(used.get(nx, 0) + 1, L + 1):
            extend(word + [(nx, nq)], S, L, best)
def job(args):
    S, L, first = args
    best = [None, None, None]
    extend([first], S, L, best)
    return best
if __name__ == '__main__':
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    L = (4 * S - 1) // 5
    starts = [(x, q) for x in (1, 2, 3) for q in range(1, L + 1)]
    print(f'order 5 certificate (strict): spread bound S = {S}, lap bound L = {L}, words to {3*L} moves')
    with Pool() as pool:
        res = pool.map(job, [(S, L, s) for s in starts])
    cand = [b for b in res if b[0] is not None]
    if cand:
        best = max(cand, key=lambda b: b[0])
        print(f'   largest sup R over realisable words: {best[0]} = {float(best[0]):.4f}   word {best[1]}   margin tau = {best[2]}')
        print(f'   target sup R < 4  ->  {"PROVED for spread <= " + str(S) if best[0] < 4 else "NOT proved"}')
    else:
        print('   no realisable word — cascade cannot move at this spread bound')
