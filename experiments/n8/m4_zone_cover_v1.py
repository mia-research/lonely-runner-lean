#!/usr/bin/env python3
"""m4_zone_cover_v1 -- NoCarve on an M4 box as an exact covering by gap-pattern zones.

Object.  Readings g_0..g_6 with g_0 = 1 (the pin), g_s in the face [a_s, b_s] of the box.
A gap pattern m = (m_0 = 0, m_1, ..., m_6): reading s in [8m_s+1, 8m_s+7] at the instant R.
For fixed m the set of g having such an R is the zone
    C_m = { g : g_s / g_r <= (8m_s+7)/(8m_r+1) for all r != s }
(take R = max_r (8m_r+1)/g_r; the pair conditions are exactly R <= (8m_s+7)/g_s; s = 0 gives
R in [1,7]).  So NoCarve on the box  <=>  box contained in the union of the C_m.

Zones are multiplicative difference-bound matrices U[r][s] = upper bound on g_s/g_r (closed),
closed by Floyd-Warshall.  Tree: a zone Z is a LEAF if Z is inside one C_m (pairwise test on the
closure, exact); otherwise choose m with int(C_m and Z) nonempty and CUT Z along a facet
g_s/g_r = c of C_m that crosses the interior of Z, children Z and (<= c), Z and (>= c).
Every cut is a facet of a C_m, so a branch terminates; a full-dimensional zone meeting no C_m
in its interior is reported UNCOVERED (it would contain reading vectors with no clear instant
in [1,7]).  Exact Fractions throughout."""
import sys, json
from fractions import Fraction as F

N = 7
def face(v):
    return (F(max(2 * v - 1, 2), 2), F(2 * v + 1, 2))

def closure(U):
    U = [row[:] for row in U]
    for k in range(N):
        for r in range(N):
            if U[r][k] is None: continue
            for s in range(N):
                if U[k][s] is None: continue
                v = U[r][k] * U[k][s]
                if U[r][s] is None or v < U[r][s]: U[r][s] = v
    return U

def box_zone(n):
    U = [[None] * N for _ in range(N)]
    for r in range(N): U[r][r] = F(1)
    for s in range(1, N):
        a, b = face(n[s]); U[0][s] = b; U[s][0] = 1 / a
    return closure(U)

def full_dim(U):
    """every nontrivial 2-cycle product > 1 (U closed => enough)"""
    for r in range(N):
        for s in range(r + 1, N):
            if U[r][s] * U[s][r] <= 1: return False
    return True

def add(U, r, s, c):
    V = [row[:] for row in U]
    if V[r][s] is None or c < V[r][s]: V[r][s] = c
    return closure(V)

def cm(mr, ms):
    return F(8 * ms + 7, 8 * mr + 1)

def doms(U):
    D = [[0]]
    for s in range(1, N):
        hi = U[0][s]; lo = 1 / U[s][0]
        # C_m and Z share interior points only if 8m+7 > lo and 8m+1 < 7*hi
        D.append([m for m in range(0, 40) if 8 * m + 7 > lo and 8 * m + 1 < 7 * hi])
    return D

def search(U, test):
    """backtrack over m with a pairwise predicate test(r, s, mr, ms)"""
    D = doms(U); m = [0] * N
    def bt(s):
        if s == N: return True
        for v in D[s]:
            m[s] = v
            if all(test(r, s, m[r], v) for r in range(s)) and bt(s + 1): return True
        return False
    return list(m) if bt(1) else None

def leaf(U):
    return search(U, lambda r, s, mr, ms: U[r][s] <= cm(mr, ms) and U[s][r] <= cm(ms, mr))

def overlap(U):
    """an m whose zone meets int Z: pairwise interior overlap, then verified by closure."""
    best = None
    D = doms(U); m = [0] * N
    out = []
    def ok(r, s, mr, ms):
        # interval of g_s/g_r in Z: [1/U[s][r], U[r][s]];  in C_m: [1/cm(ms,mr), cm(mr,ms)]
        return max(1 / U[s][r], 1 / cm(ms, mr)) < min(U[r][s], cm(mr, ms))
    def bt(s):
        if len(out) >= 50: return
        if s == N:
            W = U
            for r in range(N):
                for t in range(N):
                    if r != t: W = W if (W[r][t] is not None and W[r][t] <= cm(m[r], m[t])) else add(W, r, t, cm(m[r], m[t]))
            if full_dim(W): out.append((list(m), W))
            return
        for v in D[s]:
            m[s] = v
            if all(ok(r, s, m[r], v) for r in range(s)): bt(s + 1)
    bt(1)
    return out

def cover(U, depth=0, stats=None, cap=10**6):
    stats["nodes"] += 1
    if stats["nodes"] > cap: raise RuntimeError("cap")
    stats["maxd"] = max(stats["maxd"], depth)
    m = leaf(U)
    if m is not None:
        stats["leaves"] += 1; return ("L", m)
    cands = overlap(U)
    if not cands:
        stats["uncovered"].append([[str(x) if x is not None else None for x in row] for row in U]); return ("U",)
    # choose the candidate whose zone keeps the most of Z: fewest crossing facets
    def crossing(m):
        out = []
        for r in range(N):
            for s in range(N):
                if r == s: continue
                c = cm(m[r], m[s])
                if 1 / U[s][r] < c < U[r][s]: out.append((r, s, c))
        return out
    m, _ = min(cands, key=lambda t: len(crossing(t[0])))
    r, s, c = crossing(m)[0]
    A = add(U, r, s, c); B = add(U, s, r, 1 / c)
    return ("C", r, s, str(c), cover(A, depth + 1, stats, cap), cover(B, depth + 1, stats, cap))

def run(n, cap=10**6):
    stats = {"nodes": 0, "leaves": 0, "maxd": 0, "uncovered": []}
    try:
        cover(box_zone(n), 0, stats, cap); st = "OK" if not stats["uncovered"] else "UNCOVERED"
    except RuntimeError:
        st = "CAP"
    return {"n": n, "status": st, "nodes": stats["nodes"], "leaves": stats["leaves"], "depth": stats["maxd"],
            "uncovered": stats["uncovered"][:2]}

if __name__ == "__main__":
    for a in sys.argv[1:]:
        print(json.dumps(run(json.loads(a))), flush=True)
