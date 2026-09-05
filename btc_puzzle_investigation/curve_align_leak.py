#!/usr/bin/env python3
"""
curve_align_leak.py  —  the leak test, run CURVE-ALIGNED (float-free).

Motivation (user, 2026-07-07): "x&y ECC-aligned, k,n,d curve-aligned, run the
same test." WP6 swept INTEGER statistics S(X,Y,n') (reduce the coordinate mod a
candidate). WP5 took GLV coords of the SCALAR d. Neither applied the GROUP
operation. This does: features are properties of the PUBLIC point under curve ops
(2P, P+G, lamP=(beta*X,Y), Legendre of coords); targets are curve-aligned images
of the decomposition — the residual point R = D*G = P - base(n,k)*G, and k*G.

Same estimator as leak_test_exact.py: exact MI ranked against a matched
permutation null, Westfall-Young min-p over the feature family, integer-decided
verdict (20*c < tot <=> corr_p<0.05). Positive + negative controls. min_bits=26
excludes the D==0 degenerate band (base-key trap). No float in the signal path;
the only float is inside mi_bits (a ranked statistic) and the display string.

Stage-1 diagnostic: targets use d (necessary condition, not an attack). If a
curve-aligned target FIRES where its integer analogue was null, curve alignment
exposed structure the integer view missed -> escalate to a public proxy (Stage 2).
If null, it BOUNDS the curve-aligned leak too (a conditional negative).

Usage: python3 curve_align_leak.py --data {real,synthetic} [--n N] [--shuffles R]
"""
import argparse, numpy as np, pandas as pd
from exact_core import best_nk, residual
from leak_test_exact import features as int_features, mi_bits, minp_pairs
from farm.lib_data import ec_mul, ec_add, ec_neg, G, P as PF, N_ORD, BETA

MODULI = [3, 5, 7, 11, 13, 256]

def qr(x):
    """Legendre symbol as {0,1}: 1 if x is a nonzero quadratic residue mod PF."""
    x %= PF
    return 1 if x and pow(x, (PF - 1) // 2, PF) == 1 else 0

def curve_features(X, Y):
    """Public group-operation features of P=(X,Y). No secret, no float."""
    f = {}
    P2 = [ec_add((x, y), (x, y)) for x, y in zip(X, Y)]     # 2P
    PG = [ec_add((x, y), G) for x, y in zip(X, Y)]           # P+G
    lam = [(BETA * x % PF, y) for x, y in zip(X, Y)]         # lambda*P = (beta X, Y)
    for m in MODULI:
        f[f"2Px%{m}"]  = np.array([px % m for (px, py) in P2])
        f[f"PGx%{m}"]  = np.array([px % m for (px, py) in PG])
        f[f"lamx%{m}"] = np.array([px % m for (px, py) in lam])
    f["2Py_par"] = np.array([py & 1 for (px, py) in P2])
    f["PGy_par"] = np.array([py & 1 for (px, py) in PG])
    f["qrX"] = np.array([qr(x) for x in X])
    f["qrY"] = np.array([qr(y) for y in Y])
    return f

def curve_targets(d, N, rng):
    """Curve-aligned images of the (n,k,D) decomposition. USES d (Stage-1 diagnostic)."""
    nk = [best_nk(int(v), int(n), 256) for v, n in zip(d, N)]
    D  = [residual(int(v), int(n), a, b) for (a, b), v, n in zip(nk, d, N)]
    # residual point R = D*G  (== P - base*G); verified below on a sample
    RG = [ec_mul(int(x) % N_ORD, G) for x in D]
    KG = [ec_mul(int(b), G) for (a, b) in nk]
    tg = {}
    tg["n_parity"] = np.array([a & 1 for a, b in nk])       # integer baselines
    tg["k_parity"] = np.array([b & 1 for a, b in nk])
    tg["Ry_par"] = np.array([(py & 1) if pt else 0 for pt in RG for py in [pt[1] if pt else 0]])
    tg["Rx_qr"]  = np.array([qr(pt[0]) if pt else 0 for pt in RG])
    tg["Rx_m7"]  = np.array([(pt[0] % 7) if pt else 0 for pt in RG])
    tg["kGy_par"] = np.array([(pt[1] & 1) if pt else 0 for pt in KG])
    tg["kGx_qr"]  = np.array([qr(pt[0]) if pt else 0 for pt in KG])
    # controls
    return tg, nk, D, RG

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", choices=["real", "synthetic"], default="real")
    ap.add_argument("--n", type=int, default=2000)
    ap.add_argument("--shuffles", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=31337)
    ap.add_argument("--min-bits", type=int, default=40)  # base-key-imprint floor (see leak_test_exact)
    a = ap.parse_args(); rng = np.random.default_rng(a.seed)
    if a.data == "real":
        df = pd.read_csv("btc_puzzle_master_exact.csv")
        df = df[df.status == "SOLVED"].rename(columns={"priv_dec":"d","X_hex":"X","Y_hex":"Y"})
        df = df[df.bits >= a.min_bits][["bits","d","X","Y"]].reset_index(drop=True); df["d"] = df["d"].astype(str)
    else:
        df = pd.read_csv("constructed_keys_1to160_100k_exact.csv", dtype={"d": str}, low_memory=False)
        df = df[df.bits >= a.min_bits].reset_index(drop=True)
        if len(df) > a.n: df = df.sample(a.n, random_state=a.seed).reset_index(drop=True)
    d = df["d"].tolist(); N = df["bits"].tolist()
    X = [int(x, 16) for x in df["X"]]; Y = [int(y, 16) for y in df["Y"]]

    feats = {**int_features(X, Y), **curve_features(X, Y)}
    tg, nk, D, RG = curve_targets(d, N, rng)

    # correctness gate: R == P - base*G on a sample
    ok = 0
    for i in range(min(8, len(X))):
        base = (1 << (int(N[i]) - 1)) + ((1 << (int(N[i]) - 1)) * nk[i][1]) // nk[i][0]
        expect = ec_add((X[i], Y[i]), ec_neg(ec_mul(base % N_ORD, G)))
        if expect == RG[i]: ok += 1
    assert ok == min(8, len(X)), f"residual-point identity failed {ok}/8"

    # controls
    x7 = np.array([int(x) % 7 for x in X])
    tg["POS_strong"] = x7.copy()
    keep = rng.random(len(X)) < 0.10                          # noqa: float (control build)
    tg["POS_f0.10"] = np.where(keep, x7, rng.integers(0, 7, len(X)))
    for j in range(8): tg[f"NEG_{j}"] = rng.integers(0, 2, len(X))

    flist = list(feats.values())
    def run(y): return minp_pairs([(f, y) for f in flist], a.shuffles, rng)
    def line(name, res):
        b, om, c, tot = res
        fires = 20 * c < tot
        print(f"  {name:11s} obs_upper_count={om:5d}/{a.shuffles}  corr_p={c/tot:.4f}  {'FIRES' if fires else 'null'}")  # noqa: float

    print(f"# CURVE-ALIGNED leak test  data={a.data}  keys={len(df)}  min_bits={a.min_bits}  "
          f"features={len(flist)} (int+curve)  shuffles={a.shuffles}")
    print("CONTROLS")
    for nm in ["POS_strong", "POS_f0.10"]: line(nm, run(tg[nm]))
    negfire = sum(1 for j in range(8) if (lambda r: 20*r[2] < r[3])(run(tg[f"NEG_{j}"])))
    print(f"  NEGATIVE: {negfire}/8 fired")
    print("INTEGER BASELINE targets")
    for nm in ["n_parity", "k_parity"]: line(nm, run(tg[nm]))
    print("CURVE-ALIGNED targets (residual point D*G, and k*G)")
    for nm in ["Ry_par", "Rx_qr", "Rx_m7", "kGy_par", "kGx_qr"]: line(nm, run(tg[nm]))

if __name__ == "__main__":
    main()
