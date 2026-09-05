#!/usr/bin/env python3
"""
parametric_shadow_sweep_v1.py

User (2026-07-13): "if we move a variable from less to more we might see the shadow
move to reveal the data in noise." This is a TRANSFER-FUNCTION test: construct
families of valid 256-bit keys with ONE construction variable V swept over a grid
(others randomized), then measure whether any POINT-side statistic S(X,Y) co-moves
with V. A moving shadow => MI(V;S)>0 / the S-distribution shifts monotonically with V.

Construction variables swept (the "twist / angular movement" knobs):
  * ANGLE k/n  -- fix n, sweep the Farey numerator k (the angular coordinate of d in
    its cell). Keys constructed so best_nk(d)==(n,k) exactly (round-trip verified).
  * DEPTH |D|  -- sweep the bit-length of the residual (how deep d sits in its cell),
    n,k randomized.
Point statistics S: exact Eisenstein lift sextant, chi6(X), chi6(Y), X top-4 bits, X%7.

CALIBRATION (so a flat result MEANS something):
  (+) PLANT: V=d mod 6 with S = a leaked copy of d mod 6  -> MI must fire.
  (-) real sweeps -> expected flat (ECDLP/curve scrambles construction structure).

Detector: bias-corrected MI + permutation z (power-scaling machinery), V as target.
Also per-level mean of the sextant to SEE any shift. Exact integers in signal path.
"""
import numpy as np
from ecc_secp256k1 import scalar_mul
from exact_core import best_nk, residual, lo_of
from angular_interference_scaling_v1 import chi6, chi2, conditional, loglog_slope
from eisenstein_lift_sextant_exact_v1 import lift_sextant
import random
PY = random.Random(20260713)
N = 256; LO = lo_of(N)

def point_stats(X, Y):
    return {"sextant": lift_sextant(X), "chi6X": chi6(X) or 0, "chi6Y": chi6(Y) or 0,
            "Xtop4": (X >> (X.bit_length() - 4)) if X.bit_length() >= 4 else 0,
            "X%7": X % 7}

def construct_fixed_angle(n, k, count):
    """Keys with best_nk == (n,k) exactly (round-trip verified). Returns list of (d,X,Y)."""
    base = LO + (LO * k) // n
    W = LO // (n * n)
    out = []; tries = 0
    while len(out) < count and tries < count * 40:
        tries += 1
        D = PY.randrange(-W, W)
        d = base + D
        if not (LO <= d < 2 * LO):
            continue
        if best_nk(d, N, 256) != (n, k):
            continue
        x, y = scalar_mul(d)
        out.append((d, x, y))
    return out

def construct_fixed_depth(dbits, count):
    """Keys whose |D| has ~dbits bits (n,k random via a random d then bucket-match)."""
    out = []; tries = 0
    while len(out) < count and tries < count * 60:
        tries += 1
        d = LO + PY.randrange(LO)
        n, k = best_nk(d, N, 256)
        Dv = residual(d, N, n, k)
        if abs(Dv).bit_length() != dbits:
            continue
        x, y = scalar_mul(d)
        out.append((d, x, y))
    return out

def sweep(name, levels, batches, Bnull=200):
    """levels: list of V-values; batches: list of (list of (d,X,Y)) same length.
    Build feature=point-stat, target=level index; MI over growing M."""
    print(f"\n=== SWEEP: {name}  ({len(levels)} levels, "
          f"{sum(len(b) for b in batches)} keys) ===")
    # assemble arrays
    stat_names = ["sextant", "chi6X", "chi6Y", "Xtop4", "X%7"]
    feats = {s: [] for s in stat_names}; V = []
    means_sextant = []
    for lvl, batch in zip(levels, batches):
        sx = []
        for (d, X, Y) in batch:
            ps = point_stats(X, Y)
            for s in stat_names:
                feats[s].append(ps[s])
            V.append(lvl)
            sx.append(ps["sextant"])
        means_sextant.append(sum(sx) / max(len(sx), 1))  # noqa: float (report)
    V = np.array(V, dtype=np.int64)
    # normalize V to contiguous level index for MI target
    uniq = {v: i for i, v in enumerate(sorted(set(V.tolist())))}
    Vt = np.array([uniq[v] for v in V.tolist()], dtype=np.int64)
    print(f"  per-level mean sextant (watch for a MONOTONE shift = moving shadow):")
    print("   " + "  ".join(f"{lvl}:{m:.2f}" for lvl, m in zip(levels, means_sextant)))
    rng = np.random.default_rng(7)
    M = len(Vt); Ms = [m for m in (2000, 5000, 10000, M) if m <= M]
    print(f"  MI(point-stat ; V) bias-corr I_c and z at M={M}:")
    for s in stat_names:
        f = np.array(feats[s], dtype=np.int64)
        # shuffle so levels are interleaved before truncation
        perm = rng.permutation(M); f = f[perm]; Vp = Vt[perm]
        res = conditional(f, Vp, Ms, Bnull, rng)
        Ic = [r[1] for r in res]; z = [r[2] for r in res]
        s_mi = loglog_slope(Ms, Ic)
        tag = "SHADOW" if (z[-1] > 4 and s_mi > -0.5) else "flat"  # noqa: float (classifier)
        print(f"    {s:8} vs V: I_c={Ic[-1]:+.5f}  z={z[-1]:+.2f}  slope={s_mi:+.2f} => {tag}")

def main():
    print("Parametric shadow-sweep: move a construction variable, watch the point.")

    # (+) PLANT control: V=d%6, feature = leaked copy -> must fire
    print("\n=== CONTROL(+) PLANT: V=d%6 with a leaked stat (detector sanity) ===")
    ds = [LO + PY.randrange(LO) for _ in range(8000)]
    pts = [scalar_mul(d) for d in ds]
    Vp = np.array([d % 6 for d in ds]); leaked = np.array([d % 6 for d in ds])
    rng = np.random.default_rng(1)
    res = conditional(leaked, Vp, [2000, 8000], 200, rng)
    print(f"  leaked(d%6) vs V=d%6: I_c={res[-1][1]:+.4f} z={res[-1][2]:+.1f}  (must fire big)")
    # and a real point stat vs d%6 (expected flat)
    sx = np.array([lift_sextant(x) for x, y in pts])
    res2 = conditional(sx, Vp, [2000, 8000], 200, rng)
    print(f"  sextant     vs V=d%6: I_c={res2[-1][1]:+.4f} z={res2[-1][2]:+.1f}  (expected flat)")

    # SWEEP 1: angle k/n at fixed n=7
    n = 7
    ks = [1, 2, 3, 4, 5, 6]
    batches = [construct_fixed_angle(n, k, 2500) for k in ks]
    sweep(f"ANGLE k/{n} (fixed n={n}, sweep numerator k)", ks, batches)

    # SWEEP 2: residual depth |D| bit-length
    depths = [230, 236, 242, 248, 252]
    dbatches = [construct_fixed_depth(db, 2500) for db in depths]
    dbatches = [b for b in dbatches]
    got = [len(b) for b in dbatches]
    print(f"\n(depth batches filled: {dict(zip(depths, got))})")
    sweep("DEPTH |D| bit-length (sweep residual magnitude)",
          depths, dbatches)

if __name__ == "__main__":
    main()
