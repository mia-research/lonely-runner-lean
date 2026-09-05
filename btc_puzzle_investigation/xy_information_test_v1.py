#!/usr/bin/env python3
"""
xy_information_test_v1.py  —  Does (X,Y) leak the private key d?

Implements the design in xy_information_test_design_v1.md:
  - features from (X, Y, N) ONLY (no secret d, no secret n)  -> no circularity
  - targets = functions of the secret d (residues, positional bits, band position)
  - PLANTED controls prove detector sensitivity (the thing GECT lacked)
  - contingency-table MI (bits) + permutation null with look-elsewhere over features
  - sensitivity floor from a family of weak plants

Usage:
  python xy_information_test_v1.py --data synthetic --n 20000 --shuffles 2000
  python xy_information_test_v1.py --data real       --shuffles 5000
"""
import argparse, numpy as np, pandas as pd

P_FIELD = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA    = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
MODULI  = [2,3,4,5,7,8,9,11,13,16,25,32,64,256]
RESIDUE_TARGET_MODS = [2,3,5,7,11,13]

def mi_bits(a, b):
    """Mutual information I(a;b) in bits for integer-coded arrays a,b."""
    nb = int(b.max()) + 1
    idx = a.astype(np.int64) * nb + b.astype(np.int64)
    joint = np.bincount(idx, minlength=(int(a.max())+1)*nb).reshape(-1, nb).astype(float)
    n = joint.sum(); joint /= n
    px = joint.sum(1, keepdims=True); py = joint.sum(0, keepdims=True)
    with np.errstate(divide='ignore', invalid='ignore'):
        t = joint * (np.log2(joint) - np.log2(px) - np.log2(py))
    return np.nansum(t[joint > 0])

def hamming(v): return bin(int(v)).count("1")

def is_prime(n):
    n = int(n)
    if n < 2: return 0
    i = 2
    while i * i <= n:
        if n % i == 0: return 0
        i += 1
    return 1

def euler_phi(n):
    n = int(n); r = n; p = 2; m = n
    while p * p <= m:
        if m % p == 0:
            while m % p == 0: m //= p
            r -= r // p
        p += 1
    if m > 1: r -= r // m
    return r

def build(df):
    """Return feature dict {name: int-code array} and (d, N, X, Y) arrays."""
    d = df["d"].to_numpy(object)
    N = df["bits"].to_numpy()
    X = np.array([int(x, 16) for x in df["X"]], dtype=object)
    Y = np.array([int(y, 16) for y in df["Y"]], dtype=object)
    feats = {}
    for m in MODULI:
        feats[f"X%{m}"] = np.array([int(x) % m for x in X])
        feats[f"Y%{m}"] = np.array([int(y) % m for y in Y])
    # curve-aware public views
    for m in [7, 13, 256]:
        feats[f"phiX%{m}"] = np.array([(BETA * int(x) % P_FIELD) % m for x in X])   # GLV endo
        feats[f"negY%{m}"] = np.array([(P_FIELD - int(y)) % m for y in Y])          # -P
    # joint residues (Channel C: a pair can leak when neither coord alone does)
    for m in [2, 3, 5, 7]:
        feats[f"XY%{m}"] = np.array([(int(x) % m) * m + (int(y) % m) for x, y in zip(X, Y)])
    # magnitudes / position of the coordinate within [0,p)
    feats["Xtop8"] = np.array([(int(x) * 256) // P_FIELD for x in X])
    feats["Ytop8"] = np.array([(int(y) * 256) // P_FIELD for y in Y])
    feats["hamX"]  = np.array([hamming(x) for x in X])
    feats["hamY"]  = np.array([hamming(y) for y in Y])
    return feats, d, N, X, Y

def make_targets(d, N, X, rng, n_arr=None, k_arr=None):
    tg = {}
    for m in RESIDUE_TARGET_MODS:
        tg[f"d%{m}"] = np.array([int(v) % m for v in d])
    tg["bit_mid"]  = np.array([(int(v) >> (int(n)//2)) & 1 for v, n in zip(d, N)])
    tg["bit_top2"] = np.array([(int(v) >> max(int(n)-2, 0)) & 1 for v, n in zip(d, N)])
    # band position u in [0,1) -> 8 bins, only where N>=8
    ub = np.full(len(d), -1)
    for i, (v, n) in enumerate(zip(d, N)):
        if int(n) >= 8:
            lo = 1 << (int(n) - 1)
            ub[i] = min(int(8 * (int(v) - lo) / lo), 7)
    tg["u_bin8"] = ub  # -1 rows dropped per-cell
    # --- n/k channel: does (X,Y) leak the number-theoretic coordinate or its phi-harmonic? ---
    if n_arr is not None:
        nn = [int(x) for x in n_arr]; kk = [int(x) for x in k_arr]
        ph = [euler_phi(x) for x in nn]
        tg["n_even"]   = np.array([x % 2 for x in nn])
        tg["n_mod3"]   = np.array([x % 3 for x in nn])
        tg["n_mod5"]   = np.array([x % 5 for x in nn])
        tg["n_prime"]  = np.array([is_prime(x) for x in nn])
        tg["n_bucket"] = np.array([min(x // 32, 7) for x in nn])       # coarse magnitude of n
        tg["n_dense"]  = np.array([x for x in nn])                     # full n (256 classes, weak power)
        tg["phin_mod2"] = np.array([x % 2 for x in ph])               # phi(n) harmonic
        tg["phin_mod3"] = np.array([x % 3 for x in ph])
        tg["phin_bkt"]  = np.array([min(x // 32, 7) for x in ph])
        tg["k_even"]   = np.array([x % 2 for x in kk])
        tg["k_mod3"]   = np.array([x % 3 for x in kk])
    # planted controls: strong (deterministic in X) + weak family (calibrate floor)
    xmod7 = np.array([int(x) % 7 for x in X])
    tg["PLANT_strong"] = xmod7.copy()
    for f in [0.02, 0.05, 0.10, 0.20]:
        noisy = rng.integers(0, 7, size=len(X))
        keep = rng.random(len(X)) < f
        tg[f"PLANT_f{f:.2f}"] = np.where(keep, xmod7, noisy)
    return tg

def eval_target(y, feats, R, rng):
    """Per-feature MI standardized against its OWN permutation null (z-score), so
    features of different cardinality compare fairly (raw MI is biased upward by
    ~(bx-1)(by-1)/(2n ln2) for high-cardinality features). Statistic = max-z over
    features; look-elsewhere-corrected p = null distribution of that max-z."""
    mask = y >= 0
    y = y[mask]
    names = list(feats); fs = [feats[k][mask] for k in names]
    obs = np.array([mi_bits(v, y) for v in fs])
    null = np.empty((R, len(fs)))
    for s in range(R):
        yp = rng.permutation(y)
        null[s] = [mi_bits(v, yp) for v in fs]
    mu = null.mean(0); sd = null.std(0) + 1e-12
    obs_z = (obs - mu) / sd
    null_z = (null - mu) / sd
    bi = int(np.argmax(obs_z)); best_z = obs_z[bi]
    maxz_null = null_z.max(1)
    p = (int((maxz_null >= best_z).sum()) + 1) / (R + 1)
    return names[bi], obs[bi], best_z, p

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", choices=["synthetic", "real"], default="synthetic")
    ap.add_argument("--n", type=int, default=20000)
    ap.add_argument("--shuffles", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=12345)
    ap.add_argument("--targets", choices=["d", "nk", "all"], default="nk")
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)

    if a.data == "synthetic":
        df = pd.read_csv("constructed_keys_1to160_100k.csv",
                         usecols=["bits", "d", "X", "Y", "n", "k"], dtype={"d": str})
        df = df[df["bits"] >= 8].reset_index(drop=True)
        if len(df) > a.n:
            df = df.sample(a.n, random_state=a.seed).reset_index(drop=True)
    else:
        df = pd.read_csv("btc_puzzle_master.csv")
        df = df[df["status"] == "SOLVED"].copy()
        df = df.rename(columns={"priv_dec": "d", "X_hex": "X", "Y_hex": "Y"})
        df = df[df["bits"] >= 8][["bits", "d", "X", "Y", "n", "k"]].reset_index(drop=True)
        df["d"] = df["d"].astype(str)

    feats, d, N, X, Y = build(df)
    tg = make_targets(d, N, X, rng, n_arr=df["n"].to_numpy(), k_arr=df["k"].to_numpy())
    d_names  = [f"d%{m}" for m in RESIDUE_TARGET_MODS] + ["bit_mid", "bit_top2", "u_bin8"]
    nk_names = ["n_even","n_mod3","n_mod5","n_prime","n_bucket","n_dense",
                "phin_mod2","phin_mod3","phin_bkt","k_even","k_mod3"]
    chosen = {"d": d_names, "nk": nk_names, "all": d_names + nk_names}[a.targets]
    print(f"# data={a.data}  keys={len(df)}  features={len(feats)}  shuffles={a.shuffles}  targets={a.targets}\n")
    print(f"{'target':14s} {'best_feature':10s} {'MI_bits':>9s} {'maxz':>7s} {'corr_p':>8s}   verdict")
    print("-" * 70)
    floor = None
    order = ["PLANT_strong"] + [k for k in tg if k.startswith("PLANT_f")] + chosen
    for name in order:
        bf, mi, z, p = eval_target(tg[name], feats, a.shuffles, rng)
        verdict = "FIRES" if p < 0.05 else "null"
        if name.startswith("PLANT_f") and p < 0.05:
            floor = mi if floor is None else min(floor, mi)
        tag = "  <-- control" if name.startswith("PLANT") else ""
        print(f"{name:14s} {bf:10s} {mi:9.5f} {z:7.2f} {p:8.4f}   {verdict}{tag}")
    print("-" * 70)
    if floor is not None:
        print(f"sensitivity floor  ~ {floor:.5f} bits  (smallest weak-plant MI that fired)")
    print(f"Any {a.targets}-target FIRES => investigate (OOS + candidate-sweep attack translation).")
    print(f"All {a.targets}-targets null => bounded: no (X,Y)->{a.targets} leak above the floor, this feature set.")

if __name__ == "__main__":
    main()
