#!/usr/bin/env python3
"""
nk_channel_scaling.py  —  final scaling-law verdict on the n/k channel.

The n/k channel (predict n from (X,Y), max over feature x nmax) fired 2/4 seeds but
on WANDERING winning cells: (XY%3, nmax=160) @seed31337, (Ytop8, nmax=64) @seed22.
Multi-seed said "unstable"; this asks the sharper question via power_scaling:

  Does a winning cell's bias-corrected MI PLATEAU (real leak, z ~ sqrt(N)) or DECAY
  ~1/N (noise, z flat, tracking a shuffled-n control)?

We scale (a) each firing cell with REAL n, (b) the same cell with n SHUFFLED (neg
control), (c) the whole-channel max-I_c over all 42x31 cells, real vs shuffled. If
real tracks shuffled and both decay, the channel is noise -- final verdict.

Exact int signal path; MI/z are ranked/diagnostic floats only.

Usage: python3 nk_channel_scaling.py [--Bnull 300]
"""
import argparse, numpy as np, pandas as pd
from exact_core import nk_curve
from leak_test_exact import features as int_features, mi_bits
from power_scaling import scaling, loglog_slope, z_sqrtN_slope

NS = [500, 1000, 2000, 5000, 10000, 20000, 40000]
NMAXG = list(range(32, 513, 16))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--Bnull", type=int, default=300)
    ap.add_argument("--seed", type=int, default=31337)
    a = ap.parse_args(); rng = np.random.default_rng(a.seed)
    df = pd.read_csv("constructed_keys_1to160_100k_exact.csv", dtype={"d": str}, low_memory=False)
    df = df[df.bits >= 40].reset_index(drop=True)
    Nmax = min(max(NS), len(df)); NSs = [n for n in NS if n <= Nmax]
    df = df.iloc[:Nmax].reset_index(drop=True)
    d = df["d"].tolist(); N = df["bits"].tolist()
    X = [int(x, 16) for x in df["X"]]; Y = [int(y, 16) for y in df["Y"]]
    P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
    feat = {"XY%3": np.array([(int(x) % 3) * 3 + (int(y) % 3) for x, y in zip(X, Y)]),
            "Ytop8": np.array([(int(y) * 256) // P for y in Y])}
    ncur = [nk_curve(int(v), int(n)) for v, n in zip(d, N)]
    nt = {160: np.array([c[160] for c in ncur]), 64: np.array([c[64] for c in ncur])}

    def const_target(arr):
        return lambda n, rng: arr[:n]
    def shuf_target(arr):
        return lambda n, rng: arr[rng.permutation(n)]

    print(f"# n/k CHANNEL scaling verdict  Bnull={a.Bnull}   NS={NSs}")
    print("# SIGNAL: I_c plateau (loglog slope ~0) & z ~ sqrt(N).  NOISE: I_c ~1/N & z flat.\n")
    for fname, nmax in [("XY%3", 160), ("Ytop8", 64)]:
        f = feat[fname]; tgt = nt[nmax]
        for tag, tfn in [("REAL n", const_target(tgt)), ("SHUFFLED n (ctrl)", shuf_target(tgt))]:
            res = scaling(f, tfn, NSs, a.Bnull, rng)
            Ic = [r[1] for r in res]; z = [r[2] for r in res]
            s_mi = loglog_slope(NSs, Ic); s_z = z_sqrtN_slope(NSs, z)
            verdict = "SIGNAL" if (s_mi > -0.5 and s_z > 0) else "noise"   # noqa: float (slope classifier)
            print(f"[{fname} x n(nmax={nmax})  {tag:17s}]")
            print("   I_c :" + "".join(f"{v:11.5f}" for v in Ic))
            print("   z   :" + "".join(f"{v:11.2f}" for v in z))
            print(f"   -> loglog-slope(I_c)={s_mi:+.2f}  z-slope={s_z:+.4f}  => {verdict}\n")

if __name__ == "__main__":
    main()
