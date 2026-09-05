#!/usr/bin/env python3
"""
build_fullrange_dataset_v1.py

Replace the 160-bit-capped constructed_keys_1to160_100k set (whose low bit range
was a false clarifier -- MT twist-horizon result 2026-07-13) with a FULL-RANGE
known-d dataset weighted to 256 bits (the range Bitcoin/secp256k1 actually uses,
where GLV is non-degenerate).  All keys are computed by us with known d, so they
are valid for every CURVE-side question and there can be as many as we want.

Each key carries d + point (X,Y) + the derived coordinates we probe:
  n,k,D      -- the exact (best-approx denominator, numerator, residual) coordinate
  a_glv,b_glv,glv_maxbits -- balanced Z[omega] GLV decomposition (2-D iff d>=2^128)
  sextant    -- exact Eisenstein 2-D lift 6-sextant (curve-fixed hexagonal angle)
  chi6X,chi6Y,chi2Y       -- CM sextic / quadratic phases

Bulk at 256 bits + a spread across bit-lengths so "does less bit clarify?" can be
tested directly (it should NOT, per the twist-horizon + curve-generic results).

Exact integers in the signal path (CLAUDE.md).  Output: CSV + npz (object arrays).
Usage: python build_fullrange_dataset_v1.py [--bulk 20000] [--spread 1000] [--seed 7]
"""
import argparse, csv, os, numpy as np
from ecc_secp256k1 import scalar_mul, P as PF, N_ORDER
from exact_core import best_nk, residual
from eisenstein_lift_sextant_exact_v1 import lift_sextant
from angular_interference_scaling_v1 import chi6, chi2

# --- GLV (balanced Z[omega] decomposition), exact ---
LAM = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
def _rdiv(nu, de):
    if de < 0: nu, de = -nu, -de
    q, r = divmod(nu, de); return q + 1 if 2*r >= de else q
def _dot(u, v): return u[0]*v[0] + u[1]*v[1]
def _gauss(u, v):
    while True:
        if _dot(v, v) < _dot(u, u): u, v = v, u
        m = _rdiv(_dot(u, v), _dot(u, u)); v = (v[0]-m*u[0], v[1]-m*u[1])
        if _dot(v, v) >= _dot(u, u): return u, v
GB1, GB2 = _gauss((N_ORDER, 0), (-LAM, 1))
GDET = GB1[0]*GB2[1] - GB1[1]*GB2[0]
def glv(d):
    c1 = _rdiv(d*GB2[1], GDET); c2 = _rdiv(-d*GB1[1], GDET)
    a = d - (c1*GB1[0]+c2*GB2[0]); b = -(c1*GB1[1]+c2*GB2[1])
    return a, b

NMAX = 256

def derive(d, N):
    x, y = scalar_mul(d)
    n, k = best_nk(d, N, NMAX)
    D = residual(d, N, n, k)
    a, b = glv(d)
    gmb = max(abs(a), abs(b)).bit_length()
    return dict(N=N, d=d, X=x, Y=y, n=n, k=k, D=D, a_glv=a, b_glv=b,
                glv_maxbits=gmb, sextant=lift_sextant(x),
                chi6X=chi6(x), chi6Y=chi6(y), chi2Y=chi2(y))

def bitlen_schedule(bulk, spread):
    """Return list of (N, count): bulk at 256 + `spread` each across a bit grid."""
    grid = list(range(16, 257, 16))          # 16,32,...,256
    sched = [(256, bulk)]
    for N in grid:
        sched.append((N, spread))
    return sched

FIELDS = ["N", "d", "X", "Y", "n", "k", "D", "a_glv", "b_glv", "glv_maxbits",
          "sextant", "chi6X", "chi6Y", "chi2Y"]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bulk", type=int, default=20000, help="keys at 256 bits")
    ap.add_argument("--spread", type=int, default=1000, help="keys per grid bit-length")
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--out", default="constructed_keys_fullrange_v1")
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    sched = bitlen_schedule(a.bulk, a.spread)
    total = sum(c for _, c in sched)
    print(f"generating {total} known-d keys: bulk={a.bulk}@256 + spread={a.spread} x "
          f"{len(sched)-1} bit-lengths")
    rows = []
    done = 0
    for N, count in sched:
        lo = 1 << (N - 1)
        for _ in range(count):
            d = lo + int.from_bytes(rng.bytes((N + 7)//8), "big") % lo
            rows.append(derive(d, N))
            done += 1
            if done % 5000 == 0:
                print(f"  {done}/{total}")
    # CSV (exact: d decimal, X/Y hex)
    here = os.path.dirname(os.path.abspath(__file__))
    csv_path = os.path.join(here, a.out + ".csv")
    with open(csv_path, "w", newline="") as f:
        w = csv.writer(f); w.writerow(FIELDS)
        for r in rows:
            w.writerow([r["N"], r["d"], f'{r["X"]:x}', f'{r["Y"]:x}', r["n"], r["k"],
                        r["D"], r["a_glv"], r["b_glv"], r["glv_maxbits"], r["sextant"],
                        r["chi6X"], r["chi6Y"], r["chi2Y"]])
    # npz (object arrays keep big ints exact)
    npz_path = os.path.join(here, a.out + ".npz")
    cols = {k: np.array([r[k] for r in rows], dtype=object) for k in FIELDS}
    np.savez(npz_path, **cols)
    print(f"wrote {csv_path}\nwrote {npz_path}\n")
    # quick sanity: GLV degeneracy by bit-length (b~0 below 2^128)
    import collections
    by = collections.defaultdict(lambda: [0, 0])
    for r in rows:
        by[r["N"]][0] += 1
        if abs(r["b_glv"]) >= (1 << 100):
            by[r["N"]][1] += 1
    print("bit-length : frac with |b_glv|>=2^100 (GLV genuinely 2-D)")
    for N in sorted(by):
        tot, nd = by[N]
        print(f"  N={N:3d}: {nd}/{tot}")

if __name__ == "__main__":
    main()
