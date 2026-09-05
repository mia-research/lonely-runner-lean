#!/usr/bin/env python3
"""
leak_test_exact.py  —  float-free (X,Y)->key leakage test (CLAUDE.md rule).

Signal path (features, targets, decomposition, permutation, p-values) is exact
int. The ONLY float is inside mi_bits(), a monotone statistic ranked against a
matched permutation null — the sanctioned exception; those lines carry # noqa: float.

Estimator: Westfall-Young min-p (rank-based) over the feature family, so a
high-cardinality feature's larger raw MI is judged against its OWN null — no
z-scores, cardinality-robust, exact integer ranks. n/k channel prices the nmax
search by making (feature x nmax) the family. Positive + negative controls.

Targets recomputed from d with exact_core, INCLUDING the low-bit targets that
float previously deleted (residual D bits, d_terms, deep CF).

Usage: python leak_test_exact.py --data {real,synthetic} [--n N] [--shuffles R]
"""
import argparse, numpy as np, pandas as pd
from exact_core import best_nk, residual, d_terms, cf_denoms, position_bin, nk_curve

P_FIELD = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA    = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
MODULI  = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 25, 32, 64, 256]
NMAXG   = list(range(32, 513, 16))

def mi_bits(a, b):
    """MI in bits of integer-coded arrays. Float here is a ranked statistic only."""
    nb = int(b.max()) + 1
    joint = np.bincount(a * nb + b, minlength=(int(a.max()) + 1) * nb).reshape(-1, nb)
    n = int(joint.sum())
    Pr = joint / n                                                   # noqa: float
    px = Pr.sum(1, keepdims=True); py = Pr.sum(0, keepdims=True)
    with np.errstate(divide="ignore", invalid="ignore"):
        t = Pr * (np.log2(Pr) - np.log2(px) - np.log2(py))           # noqa: float
    return float(np.nansum(t[Pr > 0]))                               # noqa: float

def ham(v): return bin(int(v)).count("1")

def features(X, Y):
    f = {}
    for m in MODULI:
        f[f"X%{m}"] = np.array([int(x) % m for x in X])
        f[f"Y%{m}"] = np.array([int(y) % m for y in Y])
    for m in (7, 13, 256):
        f[f"phiX%{m}"] = np.array([(BETA * int(x) % P_FIELD) % m for x in X])
        f[f"negY%{m}"] = np.array([(P_FIELD - int(y)) % m for y in Y])
    for m in (2, 3, 5, 7):
        f[f"XY%{m}"] = np.array([(int(x) % m) * m + (int(y) % m) for x, y in zip(X, Y)])
    f["Xtop8"] = np.array([(int(x) * 256) // P_FIELD for x in X])
    f["Ytop8"] = np.array([(int(y) * 256) // P_FIELD for y in Y])
    f["hamX"]  = np.array([ham(x) for x in X]); f["hamY"] = np.array([ham(y) for y in Y])
    return f

def make_targets(d, N, X, rng):
    tg = {}
    for m in (2, 3, 5, 7, 11, 13):
        tg[f"d%{m}"] = np.array([int(v) % m for v in d])
    tg["bit_mid"]  = np.array([(int(v) >> (int(n)//2)) & 1 for v, n in zip(d, N)])
    tg["bit_top2"] = np.array([(int(v) >> max(int(n)-2, 0)) & 1 for v, n in zip(d, N)])
    tg["pos_bin8"] = np.array([position_bin(int(v), int(n), 8) if int(n) >= 8 else -1
                               for v, n in zip(d, N)])
    # exact decomposition-derived
    nk = [best_nk(int(v), int(n), 256) for v, n in zip(d, N)]
    D  = [residual(int(v), int(n), a, b) for (a, b), v, n in zip(nk, d, N)]
    tg["n_parity"] = np.array([a & 1 for a, b in nk])
    tg["k_parity"] = np.array([b & 1 for a, b in nk])
    tg["Dterms"]   = np.array([d_terms(int(v), int(n), a, b) for (a, b), v, n in zip(nk, d, N)])
    # LOW-BIT targets float destroyed: residual D bits (|D| low bits)
    tg["D_par"]  = np.array([abs(x) & 1 for x in D])
    tg["D_bit1"] = np.array([(abs(x) >> 1) & 1 for x in D])
    tg["D_bit4"] = np.array([(abs(x) >> 4) & 1 for x in D])
    tg["D_sign"] = np.array([1 if x >= 0 else 0 for x in D])
    # deep CF
    cf = [cf_denoms(int(v), int(n)) for v, n in zip(d, N)]
    tg["q1_par"] = np.array([qs[0] & 1 for qs in cf])
    tg["q2_par"] = np.array([(qs[1] if len(qs) > 1 else qs[0]) & 1 for qs in cf])
    tg["q3_par"] = np.array([(qs[2] if len(qs) > 2 else qs[-1]) & 1 for qs in cf])
    tg["cflen_par"] = np.array([len(qs) & 1 for qs in cf])
    # controls
    x7 = np.array([int(x) % 7 for x in X]); tg["POS_strong"] = x7.copy()
    for fr in (0.05, 0.10, 0.20):                                    # noqa: float
        keep = rng.random(len(X)) < fr                              # noqa: float
        tg[f"POS_f{fr:.2f}"] = np.where(keep, x7, rng.integers(0, 7, len(X)))
    for j in range(8):
        tg[f"NEG_{j}"] = rng.integers(0, 2, len(X))
    return tg, [nk_curve(int(v), int(n)) for v, n in zip(d, N)]

def minp_pairs(pairs, R, rng):
    """Westfall-Young min-p over a family of (x,y) columns. Shared permutation of the
    row index decouples every y from its x. Returns (best_idx, obs_min_count, corr_p)."""
    n = len(pairs[0][0])
    obs = np.array([mi_bits(x, y) for x, y in pairs])
    F = len(pairs); null = np.empty((R, F))
    for s in range(R):
        perm = rng.permutation(n)
        null[s] = [mi_bits(x, y[perm]) for x, y in pairs]
    ge = (null >= obs).sum(0)                       # per-column upper-tail count (integer)
    obs_min = int(ge.min()); best = int(np.argmin(ge))
    ranks = np.empty((R, F), dtype=int)             # rank of each null value in its column
    for f in range(F):
        col = null[:, f]; order = col.argsort()[::-1]
        r = np.empty(R, dtype=int); r[order] = np.arange(1, R + 1); ranks[:, f] = r
    null_min = ranks.min(1)
    # WY min-p: Tobs=(1+obs_min)/(R+1), T*_s=null_min[s]/R; count T*_s <= Tobs exactly
    corr = int((null_min * (R + 1) <= (obs_min + 1) * R).sum())
    return best, obs_min, (corr + 1), R + 1

def run(y, feats, R, rng):
    return minp_pairs([(f, y) for f in feats], R, rng)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", choices=["real", "synthetic"], default="real")
    ap.add_argument("--n", type=int, default=20000)
    ap.add_argument("--shuffles", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=31337)
    # min-bits floor excludes the base-key-imprint band. Exact D==0 ends at N=25, but
    # the imprint has a TAIL: for N<~40, |n*D|~2^16-22 so d~=base(n,k) tightly and
    # (X,Y) coord features still spuriously imprint n/k/D-derived targets (verified:
    # k_parity & kGx_qr fire at floor 26/32, go null at 40, different driver each
    # subsample = look-elsewhere). Default 40 keeps all decomposition targets honest;
    # pass a lower --min-bits only to reproduce the trap.
    ap.add_argument("--min-bits", type=int, default=40)
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
    feats = list(features(X, Y).values())
    tg, ncurves = make_targets(d, N, X, rng)

    def line(name, res):
        b, om, c, tot = res
        fires = 20 * c < tot                     # exact: corr_p < 0.05  <=>  c/tot < 1/20
        p = c / tot                              # noqa: float  (display only, never decides)
        print(f"  {name:12s} obs_upper_count={om:5d}/{a.shuffles}  corr_p={p:.4f}  {'FIRES' if fires else 'null'}")  # noqa: float

    print(f"# EXACT leak test  data={a.data}  keys={len(df)}  min_bits={a.min_bits}  features={len(feats)}  shuffles={a.shuffles}")
    print("CONTROLS");
    for nm in ["POS_strong","POS_f0.05","POS_f0.10","POS_f0.20"]: line(nm, run(tg[nm], feats, a.shuffles, rng))
    negfire = 0
    for j in range(8):
        b, om, c, tot = run(tg[f"NEG_{j}"], feats, a.shuffles, rng)
        if 20 * c < tot: negfire += 1            # exact: corr_p < 0.05, integer-decided
    print(f"  NEGATIVE: {negfire}/8 fired (family-wise FPR check)")
    print("TARGETS (exact; incl. low-bit D / d_terms / deep CF that float destroyed)")
    for nm in ["d%2","d%3","d%5","d%7","d%11","d%13","bit_mid","bit_top2","pos_bin8",
               "n_parity","k_parity","Dterms","D_par","D_bit1","D_bit4","D_sign",
               "q1_par","q2_par","q3_par","cflen_par"]:
        line(nm, run(tg[nm], feats, a.shuffles, rng))
    print("n/k CHANNEL (nmax search priced in)")
    pairs = [(f, np.array([c[nm] for c in ncurves])) for f in feats for nm in NMAXG]
    b, om, c, tot = minp_pairs(pairs, a.shuffles, rng)
    fires = 20 * c < tot                         # exact integer verdict
    p = c / tot                                  # noqa: float  (display only, never decides)
    print(f"  max over feature x nmax: obs_upper_count={om}/{a.shuffles}  corr_p={p:.4f}  {'FIRES' if fires else 'null'}")  # noqa: float

if __name__ == "__main__":
    main()
