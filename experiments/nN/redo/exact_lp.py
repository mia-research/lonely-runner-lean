"""Exact linear programming (Fractions), Chvatal-style dictionary simplex with Bland's rule.
lp_max(A, b, c): maximise c.x subject to A x <= b, x >= 0.  Returns ('infeasible',), ('unbounded',) or ('opt', value, x)."""
from fractions import Fraction as F

def _pivot(D, basis, nonbasis, r, e):
    # D: rows [const, coeffs over nonbasis]; row i means basis[i] = D[i][0] + sum_j D[i][j+1] * nonbasis[j]
    row = D[r]; a = row[e + 1]
    new = [-row[0] / a] + [-v / a for v in row[1:]]
    new[e + 1] = F(1) / a
    D[r] = new
    for i, R in enumerate(D):
        if i == r: continue
        f = R[e + 1]
        if f != 0:
            R[0] += f * new[0]
            for j in range(1, len(R)):
                R[j] = (f * new[j]) if j == e + 1 else R[j] + f * new[j]
    basis[r], nonbasis[e] = nonbasis[e], basis[r]

def _simplex(D, obj, basis, nonbasis):
    # obj: [const, coeffs over nonbasis]; maximise
    while True:
        cand = [j for j in range(len(nonbasis)) if obj[j + 1] > 0]
        if not cand: return 'opt'
        e = min(cand, key=lambda j: nonbasis[j])
        best = None
        for i, R in enumerate(D):
            if R[e + 1] < 0:
                ratio = R[0] / (-R[e + 1])
                if best is None or ratio < best[0] or (ratio == best[0] and basis[i] < basis[best[1]]): best = (ratio, i)
        if best is None: return 'unbounded'
        r = best[1]; a = D[r][e + 1]
        _pivot(D, basis, nonbasis, r, e)
        # update objective
        f = obj[e + 1]; new = D[r]
        obj[0] += f * new[0]
        for j in range(1, len(obj)):
            obj[j] = (f * new[j]) if j == e + 1 else obj[j] + f * new[j]

def lp_max(A, b, c):
    m, n = len(A), len(c)
    # variables 0..n-1 original, n..n+m-1 slacks, n+m artificial x0
    x0 = n + m
    nonbasis = list(range(n)) + [x0]
    basis = list(range(n, n + m))
    D = [[F(b[i])] + [F(-A[i][j]) for j in range(n)] + [F(1)] for i in range(m)]
    if min((F(v) for v in b), default=F(0)) < 0:
        obj = [F(0)] + [F(0)] * n + [F(-1)]
        r = min(range(m), key=lambda i: D[i][0])
        _pivot(D, basis, nonbasis, r, n)
        f = obj[n + 1]; newr = D[r]
        obj[0] += f * newr[0]
        for j in range(1, len(obj)):
            obj[j] = (f * newr[j]) if j == n + 1 else obj[j] + f * newr[j]
        _simplex(D, obj, basis, nonbasis)
        if obj[0] < 0: return ('infeasible',)
        if x0 in basis:
            r = basis.index(x0)
            e = next(j for j in range(len(nonbasis)) if D[r][j + 1] != 0)
            _pivot(D, basis, nonbasis, r, e)
    # drop x0 column
    k = nonbasis.index(x0)
    for R in D: del R[k + 1]
    del nonbasis[k]
    obj = [F(0)] + [F(0)] * len(nonbasis)
    for j, v in enumerate(nonbasis):
        if v < n: obj[j + 1] += F(c[v])
    for i, v in enumerate(basis):
        if v < n and c[v] != 0:
            f = F(c[v]); R = D[i]
            obj[0] += f * R[0]
            for j in range(1, len(obj)): obj[j] += f * R[j]
    st = _simplex(D, obj, basis, nonbasis)
    if st == 'unbounded': return ('unbounded',)
    x = [F(0)] * n
    for i, v in enumerate(basis):
        if v < n: x[v] = D[i][0]
    return ('opt', obj[0], x)

if __name__ == '__main__':
    # self-test against sympy on random small LPs
    import random
    from sympy import Rational, symbols
    from sympy.solvers.simplex import lpmax
    rnd = random.Random(1); bad = 0
    for t in range(300):
        n, m = 3, 6
        A = [[rnd.randint(-5, 5) for _ in range(n)] for _ in range(m)] + [[1 if j == i else 0 for j in range(n)] for i in range(n)]
        b = [rnd.randint(-3, 10) for _ in range(m)] + [10] * n
        c = [rnd.randint(-5, 5) for _ in range(n)]
        r = lp_max(A, b, c)
        xs = symbols('x0:%d' % n)
        cons = [sum(A[i][j] * xs[j] for j in range(n)) <= b[i] for i in range(len(A))] + [x >= 0 for x in xs]
        try:
            v, _ = lpmax(sum(c[j] * xs[j] for j in range(n)), cons); ok = (r[0] == 'opt' and r[1] == v)
        except Exception as e:
            ok = (r[0] == 'infeasible')
        if not ok: bad += 1
        if r[0] == 'opt':
            x = r[2]; assert all(sum(A[i][j] * x[j] for j in range(n)) <= b[i] for i in range(len(A))) and all(v >= 0 for v in x)
    print("self-test vs sympy lpmax on 300 random LPs: mismatches", bad)


def lp_max_dual(A, b, c):
    """As lp_max, with certificates.  ('opt', value, x, y): y >= 0 over rows, y A >= c componentwise, y.b = value.
    ('infeasible', y): y >= 0, y A >= 0, y.b < 0 (Farkas).  Certificates are checked here in exact arithmetic."""
    m, n = len(A), len(c)
    x0 = n + m
    nonbasis = list(range(n)) + [x0]
    basis = list(range(n, n + m))
    D = [[F(b[i])] + [F(-A[i][j]) for j in range(n)] + [F(1)] for i in range(m)]
    if min((F(v) for v in b), default=F(0)) < 0:
        obj = [F(0)] + [F(0)] * n + [F(-1)]
        r = min(range(m), key=lambda i: D[i][0])
        _pivot(D, basis, nonbasis, r, n)
        f = obj[n + 1]; newr = D[r]
        obj[0] += f * newr[0]
        for j in range(1, len(obj)):
            obj[j] = (f * newr[j]) if j == n + 1 else obj[j] + f * newr[j]
        _simplex(D, obj, basis, nonbasis)
        if obj[0] < 0:
            y = [F(0)] * m
            for j, v in enumerate(nonbasis):
                if n <= v < n + m: y[v - n] = -obj[j + 1]
            assert all(t >= 0 for t in y) and all(sum(y[i] * A[i][j] for i in range(m)) >= 0 for j in range(n))
            assert sum(y[i] * b[i] for i in range(m)) < 0
            return ('infeasible', y)
        if x0 in basis:
            r = basis.index(x0)
            e = next(j for j in range(len(nonbasis)) if D[r][j + 1] != 0)
            _pivot(D, basis, nonbasis, r, e)
    k = nonbasis.index(x0)
    for R in D: del R[k + 1]
    del nonbasis[k]
    obj = [F(0)] + [F(0)] * len(nonbasis)
    for j, v in enumerate(nonbasis):
        if v < n: obj[j + 1] += F(c[v])
    for i, v in enumerate(basis):
        if v < n and c[v] != 0:
            f = F(c[v]); R = D[i]
            obj[0] += f * R[0]
            for j in range(1, len(obj)): obj[j] += f * R[j]
    st = _simplex(D, obj, basis, nonbasis)
    if st == 'unbounded': return ('unbounded',)
    x = [F(0)] * n
    for i, v in enumerate(basis):
        if v < n: x[v] = D[i][0]
    y = [F(0)] * m
    for j, v in enumerate(nonbasis):
        if n <= v < n + m: y[v - n] = -obj[j + 1]
    assert all(t >= 0 for t in y)
    assert all(sum(y[i] * A[i][j] for i in range(m)) >= c[j] for j in range(n))
    assert sum(y[i] * b[i] for i in range(m)) == obj[0]
    return ('opt', obj[0], x, y)
