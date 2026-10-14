"""Order 5 finite certificate, exact. Under a first exceedance of R = 4, before that step every setting has
R = (5Q+1)/s < 4, so laps obey Q <= floor((4*S-1)/5) for readings s <= S, per-runner laps strictly increase, and the nearest
runner (reading 1) cannot set (its first setting would give R = 6).

Unknowns: the readings u2, u3, u4 in [1, S] (u1 = 1 is the nearest). A word is a sequence of (setter, lap). With
t_0 = 1/5 and t_j = (Q_j + 1/5)/u_{x_j}, the requirement that the setter is in the way just before it sets is

    | u_{x_j} (Q_{j-1} + 1/5) - Q_j u_{x_{j-1}} |  <=  u_{x_{j-1}}/5        (j >= 2)
    | u_{x_1}/5 - Q_1 | <= 1/5                                              (j = 1)

and the instants increase:  (Q_j + 1/5) u_{x_{j-1}} >= (Q_{j-1} + 1/5) u_{x_j}.  All linear in u (closed forms: a relaxation,
so the optimum bounds the true one from above). Then  sup R = (5 Q_M + 1) / min u_{x_M}  over the word's polyhedron, and the
minimum is found exactly by vertex enumeration in three variables.

Reports the largest sup R over all words, i.e. an upper bound for every order-5 arrangement of spread <= S."""
import itertools, sys
from fractions import Fraction as F
from multiprocessing import Pool
n = 5; th = F(1, n)
def solve3(rows):
    (a1, b1, c1, d1), (a2, b2, c2, d2), (a3, b3, c3, d3) = rows
    det = (a1*(b2*c3 - b3*c2) - b1*(a2*c3 - a3*c2) + c1*(a2*b3 - a3*b2))
    if det == 0: return None
    dx = (d1*(b2*c3 - b3*c2) - b1*(d2*c3 - d3*c2) + c1*(d2*b3 - d3*b2))
    dy = (a1*(d2*c3 - d3*c2) - d1*(a2*c3 - a3*c2) + c1*(a2*d3 - a3*d2))
    dz = (a1*(b2*d3 - b3*d2) - b1*(a2*d3 - a3*d2) + d1*(a2*b3 - a3*b2))
    return (dx/det, dy/det, dz/det)
def coeff(idx, val):           # reading of runner idx as a linear form in (u2,u3,u4); runner 0 is the nearest, reading 1
    v = [F(0), F(0), F(0)]; c = F(0)
    if idx == 0: c = val
    else: v[idx-1] = val
    return v, c
def lp_min(cons, obj_idx, S):
    """cons: list (a,b,c,d) meaning a*u2+b*u3+c*u4 <= d. Minimise u_{obj_idx} (0 -> constant 1)."""
    if obj_idx == 0: return F(1)
    A = list(cons)
    for i in range(3):                                   # 1 <= u_i <= S
        e = [F(0)]*3; e[i] = F(-1); A.append((e[0], e[1], e[2], F(-1)))
        e = [F(0)]*3; e[i] = F(1);  A.append((e[0], e[1], e[2], F(S)))
    best = None
    for tri in itertools.combinations(A, 3):
        p = solve3(tri)
        if p is None: continue
        if any(a*p[0] + b*p[1] + c*p[2] > d for a, b, c, d in A): continue
        v = p[obj_idx-1]
        if best is None or v < best: best = v
    return best
def constraints(word, S):
    cons = []
    x1, Q1 = word[0]
    v, c = coeff(x1, F(1, 5))                             # |u_{x1}/5 - Q1| <= 1/5
    cons.append((v[0], v[1], v[2], F(Q1) + th - c))
    cons.append((-v[0], -v[1], -v[2], -(F(Q1) - th) + c))
    for j in range(1, len(word)):
        xp, Qp = word[j-1]; xj, Qj = word[j]
        vj, cj = coeff(xj, F(Qp) + th)                    # u_{xj}(Qp+1/5)
        vp, cp = coeff(xp, F(Qj))                         # Qj u_{xp}
        vs, cs = coeff(xp, th)                            # u_{xp}/5
        a = [vj[i] - vp[i] - vs[i] for i in range(3)]; b = cs + cp - cj
        cons.append((a[0], a[1], a[2], b))
        a = [-(vj[i] - vp[i]) - vs[i] for i in range(3)]; b = cs - cp + cj
        cons.append((a[0], a[1], a[2], b))
        vA, cA = coeff(xp, F(Qj) + th)                    # (Qj+1/5) u_{xp} >= (Qp+1/5) u_{xj}
        vB, cB = coeff(xj, F(Qp) + th)
        a = [vB[i] - vA[i] for i in range(3)]; b = cA - cB
        cons.append((a[0], a[1], a[2], b))
    return cons
def extend(word, S, L, best, out):
    cons = constraints(word, S)
    if lp_min(cons, word[-1][0], S) is None: return        # infeasible word
    x, Q = word[-1]
    m = lp_min(cons, x, S)
    R = (F(5*Q + 1)) / m if m else None
    if R is not None and (best[0] is None or R > best[0]):
        best[0] = R; best[1] = list(word)
    if len(word) >= 3 * L: return
    used = {}
    for xx, QQ in word: used[xx] = QQ
    for nx in (1, 2, 3):
        lo = used.get(nx, 0) + 1
        for nq in range(lo, L + 1):
            extend(word + [(nx, nq)], S, L, best, out)
def job(args):
    S, L, first = args
    best = [None, None]
    extend([first], S, L, best, [])
    return best
if __name__ == '__main__':
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    L = (4 * S - 1) // 5
    starts = [(x, q) for x in (1, 2, 3) for q in range(1, L + 1)]
    print(f'order 5 certificate: spread bound S = {S}, lap bound L = {L}, {len(starts)} starting moves, words to {3*L} moves')
    with Pool() as pool:
        res = pool.map(job, [(S, L, s) for s in starts])
    best = max((b for b in res if b[0] is not None), key=lambda b: b[0], default=None)
    if best: print(f'   largest sup R over all words: {best[0]} = {float(best[0]):.4f}   word {best[1]}')
    print(f'   target: sup R < 4  ->  {"PROVED for this spread bound" if best and best[0] < 4 else "NOT proved"}')
