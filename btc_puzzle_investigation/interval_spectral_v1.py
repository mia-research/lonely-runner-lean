"""Spectral push: E3 is the ALL-ONES projection of C_ij = chi3(X_i - X_j).  Take the whole
spectrum instead -- sigma_max sees coherent modes ORTHOGONAL to all-ones, which E3 cannot.

The record ran this at N=82 and was resolution-limited to >=24% of the set (Marchenko-Pastur
floor).  Constructed scalars remove that limit.  Class computation stays exact integer; the SVD
is a monotone statistic RANKED against a matched null (folder rule: float allowed only this way).
"""
import random, numpy as np, sys
from interval_multireadout_v3 import (pool_pts, pool_table, jmul, N, group_classes,
                                      counts_of, stats)
from itertools import combinations

W = np.exp(2j*np.pi/3)

def C_from_table(T, sel):
    m = len(sel); A = np.zeros((m, m), dtype=complex)
    for a in range(m):
        row = T[sel[a]]
        for b in range(a+1, m):
            v = row[sel[b]]
            if v is None: continue
            z = W**(v % 3)
            A[a, b] = z; A[b, a] = z          # chi3(-1)=1 => symmetric
    return A

def C_from_xs(xs):
    from interval_multireadout_v3 import mu6
    m = len(xs); A = np.zeros((m, m), dtype=complex)
    for a in range(m):
        for b in range(a+1, m):
            v = mu6(xs[a]-xs[b])
            if v is None: continue
            z = W**(v % 3); A[a, b] = z; A[b, a] = z
    return A

def smax(A): return float(np.linalg.svd(A, compute_uv=False)[0])

def run(M, R, NP, seed, KS=(40,64,96,128,135,160,200)):
    rng = random.Random(seed)
    pool = pool_pts(NP, rng)
    print(f"  pool table ({NP} pts) ...", flush=True)
    T = pool_table(pool, "field")
    idx = list(range(NP))
    print(f"  null: R={R} SVDs of {M}x{M} ...", flush=True)
    null = sorted(smax(C_from_table(T, rng.sample(idx, M))) for _ in range(R))
    q95, q99 = null[int(.95*R)], null[int(.99*R)]
    print(f"  null sigma_max: median={null[R//2]:.2f}  95th={q95:.2f}  99th={q99:.2f}"
          f"   (Marchenko-Pastur ~ 2*sqrt(M) = {2*M**.5:.1f})")
    def pct(v): return 100.0*sum(1 for z in null if z < v)/len(null)

    # resolution calibration: plant a coherent kxk mutual-omega block INTO the matrix
    print("  -- resolution (coherent block planted into C; instrument floor, not full pipeline) --")
    base = C_from_table(T, rng.sample(idx, M))
    for kb in (8, 16, 24, 32, 48):
        A = base.copy(); A[:kb, :kb] = W; np.fill_diagonal(A, 0)
        s = smax(A)
        print(f"     block k={kb:>3} ({100*kb/M:.0f}% of set): sigma_max={s:.2f} pctile={pct(s):.1f}"
              f"  -> {'RESOLVED' if s >= q99 else 'below floor'}")
    print("  -- C-NEG --")
    xs = [jmul(rng.randrange(1, N)) for _ in range(M)]
    from interval_multireadout_v3 import batch_x
    s = smax(C_from_xs(batch_x(xs)))
    print(f"     d uniform [1,n): sigma_max={s:.2f} pctile={pct(s):.1f}"
          f"  -> {'quiet' if s < q95 else '*** FIRES -- VOID ***'}")
    if s >= q95: return
    print("  -- arms --")
    for k in KS:
        lo, hi = 2**(k-1), 2**k
        xs = batch_x([jmul(rng.randrange(lo, hi)) for _ in range(M)])
        s = smax(C_from_xs(xs))
        fl = " FIRE" if s >= q99 else ""
        print(f"     k={k:>4}  sigma_max={s:>7.2f}  pctile={pct(s):>5.1f}%{fl}", flush=True)

if __name__ == "__main__":
    print("SPECTRAL PUSH -- sigma_max of C, field difference, M=400 (record ran N=82, floor 24%)")
    run(400, 600, 1100, 20260731)
