#!/usr/bin/env sage
# delta_r_corrected_v2 -- perf-fixed (colidx dict). The NON-FORCED test: for each isotype block r of
# the sigma-invariant target-orbit ideal, delta_r = d_LF(fixed-target) - d_LF^(r)(orbit block r).
# Let the test speak: delta_r != 0 anywhere is a real degree difference to CHASE, not to explain away.
import sys, os, random as pyr
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from sage.all import *
from semaev_elimination_v1 import summation_poly, decomposition_system, macaulay_stats, _exps_le

def cube_root(F):
    for u in range(2, int(F.characteristic())):
        if F(u) != 1 and F(u)**3 == 1: return F(u)
    return None

def d_LF_plain(F, gens, xs, Dmax):
    st = macaulay_stats(F, gens, xs, Dmax)
    fell = [D for D in sorted(st) if st[D].get('fall', 0) > 0]
    return (fell[-1] if fell else None)

def blockLF(F, gens, xs, Dmax):
    """per-isotype (deg mod 3) last-fall degree; matrix is block-diagonal for sigma-(co)variant gens."""
    n = len(xs); Rring = xs[0].parent()
    prev = {0: 0, 1: 0, 2: 0}; lastfall = {0: None, 1: None, 2: None}
    for D in range(1, Dmax + 1):
        cols = list(_exps_le(n, D))
        colidx = {e: i for i, e in enumerate(cols)}          # PERF FIX: O(1) lookup
        col_iso = [sum(e) % 3 for e in cols]
        pos = {}; nblk = {0: 0, 1: 0, 2: 0}
        for i in range(len(cols)):
            r = col_iso[i]; pos[i] = nblk[r]; nblk[r] += 1
        rows = {0: [], 1: [], 2: []}
        for f in gens:
            df = f.degree()
            if df > D: continue
            for ue in _exps_le(n, D - df):
                poly = Rring.monomial(*ue) * f
                items = list(poly.dict().items())
                r = sum(next(iter(poly.dict())))  # isotype of first monomial
                r = (list(poly.dict().keys())[0]); r = sum(r) % 3
                row = {pos[colidx[tuple(e)]]: c for e, c in items}
                rows[r].append(row)
        for r in (0, 1, 2):
            if not rows[r]: continue
            top = {pos[i] for i in range(len(cols)) if col_iso[i] == r and sum(cols[i]) == D}
            M = matrix(F, len(rows[r]), nblk[r], sparse=True)
            for ri, row in enumerate(rows[r]):
                for cj, c in row.items(): M[ri, cj] = c
            rk = M.rank()
            tc = sorted(top)
            rk_top = M.matrix_from_columns(tc).rank() if tc else 0
            fall = (rk - rk_top) - prev[r]
            if fall > 0: lastfall[r] = D
            prev[r] = rk
    return lastfall

def cell(F, m, beta, seed):
    pyr.seed(int(seed)); E = EllipticCurve(F, [0, 7]); G = E.gens()[0]; N = int(E.order())
    for _ in range(400):
        pts = [int(pyr.randrange(1, N)) * G for _ in range(m)]; xc = [P[0] for P in pts]
        if any(P == E(0) for P in pts) or len(set(xc)) < m: continue
        S = E(0)
        for P in pts: S = S + P
        if -S == E(0): continue
        V = sorted({x for xx in xc for x in (xx, beta * xx, beta * beta * xx)})
        return (-S)[0], V
    return None

def run(p, m):
    F = GF(p); beta = cube_root(F)
    c = cell(F, m, beta, seed=1)
    if c is None: print(f"  p={p} m={m}: no cell", flush=True); return
    t, V = c
    print(f"  p={p} m={m} |V|={len(V)} ...", flush=True)
    Rxf, gf, xsf = decomposition_system(F, 0, 7, m, t, V)
    Dmax = 2**(m-1) + m*len(V) + 8
    dlf_fixed = d_LF_plain(F, gf, xsf, Dmax)
    print(f"    d_LF(fixed-target) = {dlf_fixed}", flush=True)
    S, zs, tt = summation_poly(F, 0, 7, m)
    vn = ['x%d' % i for i in range(1, m + 1)] + ['xT']
    R = PolynomialRing(F, vn, order='degrevlex'); g = R.gens()
    S4 = zs[0].parent().hom(list(g[:m]) + [g[m]], R)(S)
    gens = [S4] + [prod([xi - F(v) for v in V]) for xi in g[:m]] + [g[m]**3 - F(t)**3]
    lf = blockLF(F, gens, list(g), Dmax + 4)
    delta = {r: (dlf_fixed - lf[r] if (dlf_fixed is not None and lf[r] is not None) else None) for r in (0, 1, 2)}
    print(f"    blockLF(orbit) = {lf}   d_LF_whole=max_block={max([d for d in lf.values() if d], default=None)}", flush=True)
    print(f"    delta_r = {delta}   <-- NONZERO ANYWHERE = a real degree drop to CHASE", flush=True)

if __name__ == "__main__":
    run(523, 2)      # tractable warm-up (S3)
    run(523, 3)      # the target m=3 (S4)
    print("[done]", flush=True)
