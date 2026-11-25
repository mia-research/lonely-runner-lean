#!/usr/bin/env python3
"""m4_wide_blocked_v2 -- v1 with the hyperplane system solved by exact Fraction elimination (v1 used
sympy.solve, which returned a non-rational value and stopped the run).  Otherwise as v1: does each wide BUDGET box contain a BLOCKED point (m4_stall_gstar_v1's lemma)?
For each box: the retry3 checker (pin 0) run breadth-first to level 34; from the non-leaf cells at level 34, 40
taken evenly.  In each: the clear windows at the centre, each end read with the nearest reading edge; every window
bounded at both ends gives the hyperplane (8j+1) g_k = (8j'+7) g_i; with g_0 = 1, the solution's free parameters
are set to the cell centre's value (exact).  Candidate g* is then checked exactly as in m4_stall_gstar_v1:
in the cell; C(g*) finite; every point of C(g*) killed by a witness that is strict in the cell, no dyadic
coordinate used as a lower witness for one point and an upper witness for another.  A verified candidate makes
the checker's descent from that cell, hence from the box, non-terminating [P, the lemma].  Reported per box:
cells tried, candidates verified, the dimension of the solution set (6 minus the rank of the hyperplanes
with the pin removed), and the first verified g*."""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
from multiprocessing import Pool
from m4_fixedpoint_split_v1 import feasible, face, ONE

def dyadic(x):
    d = F(x).denominator
    return d & (d - 1) == 0

def kids(c):
    if feasible(c) is not None: return None
    k = max(range(1, 7), key=lambda i: (c[i][1] - c[i][0], -i))
    lo, hi = c[k]; m = (lo + hi) / 2
    a = list(c); a[k] = (lo, m); b = list(c); b[k] = (m, hi)
    return (a, b)

def nearest_edges(g, S):
    out = []
    for a, b in S:
        lo = None if a == 1 else min(((abs(a * x - (8 * ((a * x - 1) // 8) + 1)), i, 8 * int((a * x - 1) // 8) + 1) for i, x in enumerate(g)))[1:]
        hi = None if b == 7 else min(((abs(b * x - (8 * ((b * x + 1) // 8) - 1)), i, 8 * int((b * x + 1) // 8) - 1) for i, x in enumerate(g)))[1:]
        out.append((lo, hi))
    return out

def check(g, Q):
    if not all(Q[i][0] <= g[i] <= Q[i][1] for i in range(7)): return False, "outside"
    C = feasible([(x, x) for x in g]) or []
    if not C: return False, "C empty"
    if not all(a == b for a, b in C): return False, "C has an interval"
    used = {}
    for a, _ in C:
        R = a
        los = [i for i, x in enumerate(g) if (R * x).denominator == 1 and int(R * x) % 8 == 1]
        his = [i for i, x in enumerate(g) if (R * x).denominator == 1 and int(R * x) % 8 == 7]
        w = None
        for i in los:
            if Q[i][0] < g[i] and (not dyadic(g[i]) or used.get(i, 'lo') == 'lo'): w = ('lo', i); break
        if w is None:
            for k in his:
                if Q[k][1] > g[k] and (not dyadic(g[k]) or used.get(k, 'hi') == 'hi'): w = ('hi', k); break
        if w is None: return False, "point %s not killed" % R
        if dyadic(g[w[1]]): used[w[1]] = w[0]
    return True, [str(a) for a, _ in C]

def try_cell(Q):
    g = [(a + b) / 2 for a, b in Q]
    S = feasible([(x, x) for x in g]) or []
    W = nearest_edges(g, S)
    rows = []
    for lo, hi in W:
        if lo and hi:
            (i, el), (k, eh) = lo, hi
            r = [F(0)] * 7; r[k] += el; r[i] -= eh     # el*g_k - eh*g_i = 0
            rows.append(r)
    # move g_0 = 1 to the right-hand side: unknowns g_1..g_6
    A = [[r[j] for j in range(1, 7)] + [-r[0]] for r in rows]
    piv = []; m = 0
    for col in range(6):
        p = next((r for r in range(m, len(A)) if A[r][col] != 0), None)
        if p is None: continue
        A[m], A[p] = A[p], A[m]
        A[m] = [x / A[m][col] for x in A[m]]
        for r in range(len(A)):
            if r != m and A[r][col] != 0:
                f = A[r][col]; A[r] = [x - f * y for x, y in zip(A[r], A[m])]
        piv.append(col); m += 1
    if any(all(x == 0 for x in row[:6]) and row[6] != 0 for row in A):
        return {"dim": None, "ok": False, "why": "inconsistent"}
    dim = 6 - len(piv)
    x = [None] * 6
    for col in range(6):
        if col not in piv: x[col] = g[col + 1]
    for r, col in enumerate(piv):
        x[col] = A[r][6] - sum(A[r][c] * x[c] for c in range(6) if c not in piv)
    gstar = [F(1)] + x
    if any(v <= 0 for v in gstar): return {"dim": dim, "ok": False, "why": "nonpositive"}
    ok, info = check(gstar, Q)
    return {"dim": dim, "ok": ok, "why": info, "gstar": [str(v) for v in gstar], "nwin": len(W)}

if __name__ == "__main__":
    with Pool(4) as pool:
        for n in ([1, 3, 4, 5, 6, 7, 13], [1, 3, 4, 5, 6, 7, 14], [1, 4, 5, 6, 6, 8, 15]):
            faces = [face(v) for v in n]; faces[0] = (ONE, ONE)
            front = [faces]
            for L in range(34):
                res = pool.map(kids, front, chunksize=256)
                front = [x for r in res if r is not None for x in r]
            nl = [c for c, r in zip(front, pool.map(kids, front, chunksize=256)) if r is not None]
            step = max(1, len(nl) // 40)
            samp = nl[::step][:40]
            out = pool.map(try_cell, samp)
            ver = [o for o in out if o["ok"]]
            from collections import Counter
            print(json.dumps({"n": n, "level": 34, "nonleaf": len(nl), "tried": len(samp), "verified": len(ver),
                              "dims": dict(Counter(o["dim"] for o in out)), "dims_verified": dict(Counter(o["dim"] for o in ver)),
                              "fail_reasons": dict(Counter(str(o["why"])[:40] for o in out if not o["ok"])),
                              "first_verified": ver[0] if ver else None}), flush=True)
