#!/usr/bin/env python3
"""
xy_information_test_v2.py  —  corrected rerun after adversarial self-review of v1.

Fixes over v1 (see xy_information_test_review_v1.md):
  R1  Targets recomputed canonically from d (exact rational), NOT trusted from CSV.
  R2  n/k targets carry a hidden researcher DOF (the nmax cap). v1 tested nmax=256
      only; the signal spans nmax~[180,300]. v2 prices the nmax search: the n/k
      channel statistic is max standardized-MI over feature x nmax, with a MATCHED
      max-over-(feature x nmax) permutation null.
  R3  Parameter-free "n-shadow" targets added: continued-fraction convergent
      denominators q1,q2 of exact u (no nmax cap) + their parities/residues.
  R4  NEGATIVE controls: random binary targets pushed through the whole pipeline to
      measure the family-wise false-positive rate directly.
  R5  Family-wise correction over the full target grid (not per-feature only).
  R6  Exact-conditional permutation null (permute labels within the dataset,
      preserving marginals) — exact for the binary targets that matter here.

Features are (X,Y,N)-only (no secret d, no secret n) — unchanged from v1, imported.
Usage:  python xy_information_test_v2.py --data {synthetic,real} [--n N] [--shuffles R]
"""
import argparse, numpy as np, pandas as pd
from xy_information_test_v1 import build, mi_bits, RESIDUE_TARGET_MODS

NMAX_GRID = list(range(32, 513, 8))   # the nmax values a searcher could have picked

# ---------- canonical decomposition from d (exact, no CSV) ----------
def cf_convergent_denoms(num, den, cap=4):
    """Convergent denominators q1,q2,... of u=num/den in [0,1) via exact CF. Param-free.
    CF(num/den)=[a0=0; a1,a2,...]; denominator recurrence k_i=a_i k_{i-1}+k_{i-2},
    (k_{-1},k_0)=(0,1), so q1=a1, q2=a2 a1+1, ..."""
    if num == 0:
        return [1]
    a = []; x, y = num, den
    while y and len(a) < cap + 2:
        a.append(x // y); x, y = y, x % y       # a = [a0=0, a1, a2, ...]
    qs = []; km2, km1 = 0, 1
    for ai in a[1:]:                            # iterate a1, a2, ...
        k = ai * km1 + km2; qs.append(k); km2, km1 = km1, k
    return qs or [1]

def n_curve(d, N, nmax=512):
    """parity of best-approx denominator n(nmax) for nmax=1..nmax (float u, matches generator)."""
    lo = 2 ** (N - 1); u = (d - lo) / lo
    out = np.empty(nmax + 1, dtype=np.int8); be = 9e9; bn = 1
    for n in range(1, nmax + 1):
        k = round(u * n); e = abs(u - k / n)
        if e < be: be = e; bn = n
        out[n] = bn & 1
    return out

# ---------- parameter-free target battery ----------
def make_targets_v2(d, N, X, rng, n_neg=8):
    tg = {}
    for m in RESIDUE_TARGET_MODS:
        tg[f"d%{m}"] = np.array([int(v) % m for v in d])
    tg["bit_mid"]  = np.array([(int(v) >> (int(n)//2)) & 1 for v, n in zip(d, N)])
    tg["bit_top2"] = np.array([(int(v) >> max(int(n)-2, 0)) & 1 for v, n in zip(d, N)])
    ub = np.full(len(d), -1)
    for i, (v, n) in enumerate(zip(d, N)):
        if int(n) >= 8:
            lo = 1 << (int(n)-1); ub[i] = min(int(8*(int(v)-lo)/lo), 7)
    tg["u_bin8"] = ub
    # param-free n-shadow: CF convergent denominators of exact u
    q1 = []; q2 = []
    for v, n in zip(d, N):
        lo = 1 << (int(n)-1); qs = cf_convergent_denoms(int(v)-lo, lo)
        q1.append(qs[0]); q2.append(qs[1] if len(qs) > 1 else qs[0])
    q1 = np.array(q1); q2 = np.array(q2)
    tg["q1_parity"] = q1 % 2; tg["q1_mod3"] = q1 % 3
    tg["q2_parity"] = q2 % 2; tg["q2_mod3"] = q2 % 3
    # controls
    xmod7 = np.array([int(x) % 7 for x in X])
    tg["POS_strong"] = xmod7.copy()
    for f in [0.05, 0.10, 0.20]:
        noisy = rng.integers(0, 7, len(X)); keep = rng.random(len(X)) < f
        tg[f"POS_f{f:.2f}"] = np.where(keep, xmod7, noisy)
    for j in range(n_neg):                       # negative controls: pure noise, same pipeline
        tg[f"NEG_{j}"] = rng.integers(0, 2, len(X))
    return tg, [n_curve(int(v), int(n)) for v, n in zip(d, N)]

# ---------- evaluation: per-feature max-z with matched look-elsewhere null ----------
def eval_maxz(y, feat_list, R, rng):
    mask = y >= 0; y = y[mask]; fs = [f[mask] for f in feat_list]
    obs = np.array([mi_bits(v, y) for v in fs])
    null = np.empty((R, len(fs)))
    for s in range(R):
        yp = rng.permutation(y)
        null[s] = [mi_bits(v, yp) for v in fs]
    mu = null.mean(0); sd = null.std(0) + 1e-12
    zobs = (obs - mu) / sd; znull = ((null - mu) / sd).max(1)
    bi = int(np.argmax(zobs))
    return zobs[bi], (int((znull >= zobs[bi]).sum()) + 1) / (R + 1)

def eval_nk_channel(ncurves, feat_list, R, rng):
    """n/k channel: max standardized-MI over (feature x nmax) with matched null."""
    ncols = [np.array([c[nm] for c in ncurves]) for nm in NMAX_GRID]   # parity of n(nmax) per key
    cells = [(f, col) for f in feat_list for col in ncols]
    obs = np.array([mi_bits(f, col) for f, col in cells])
    null = np.empty((R, len(cells)))
    for s in range(R):
        perm = rng.permutation(len(feat_list[0]))
        pcols = [col[perm] for col in ncols]
        null[s] = [mi_bits(f, col) for f in feat_list for col in pcols]
    mu = null.mean(0); sd = null.std(0) + 1e-12
    zobs = (obs - mu) / sd; znull = ((null - mu) / sd).max(1)
    bi = int(np.argmax(zobs)); fi, nmi = divmod(bi, len(ncols))
    return zobs[bi], (int((znull >= zobs[bi]).sum()) + 1) / (R + 1), NMAX_GRID[nmi]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", choices=["synthetic", "real"], default="real")
    ap.add_argument("--n", type=int, default=20000)
    ap.add_argument("--shuffles", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=2024)
    a = ap.parse_args(); rng = np.random.default_rng(a.seed)

    if a.data == "synthetic":
        df = pd.read_csv("constructed_keys_1to160_100k.csv",
                         usecols=["bits","d","X","Y"], dtype={"d": str})
        df = df[df["bits"] >= 8].reset_index(drop=True)
        if len(df) > a.n: df = df.sample(a.n, random_state=a.seed).reset_index(drop=True)
    else:
        df = pd.read_csv("btc_puzzle_master.csv")
        df = df[df["status"] == "SOLVED"].rename(columns={"priv_dec":"d","X_hex":"X","Y_hex":"Y"})
        df = df[df["bits"] >= 8][["bits","d","X","Y"]].reset_index(drop=True); df["d"] = df["d"].astype(str)

    feats, d, N, X, Y = build(df)
    flist = list(feats.values())
    tg, ncurves = make_targets_v2(d, N, X, rng)
    print(f"# v2  data={a.data}  keys={len(df)}  features={len(flist)}  shuffles={a.shuffles}")
    print(f"# nmax grid {NMAX_GRID[0]}..{NMAX_GRID[-1]} step8 ({len(NMAX_GRID)} pts) priced into n/k channel\n")

    # controls first
    print("CONTROLS")
    for name in ["POS_strong","POS_f0.05","POS_f0.10","POS_f0.20"]:
        z,p = eval_maxz(tg[name], flist, a.shuffles, rng)
        print(f"  {name:12s} maxz={z:8.2f}  p={p:.4f}  {'FIRES' if p<0.05 else 'null'}")
    negp = [eval_maxz(tg[f'NEG_{j}'], flist, a.shuffles, rng)[1] for j in range(8)]
    print(f"  NEGATIVE (8 random binary targets): p-values {[round(x,3) for x in negp]}")
    print(f"  -> family-wise false-positive rate: {sum(p<0.05 for p in negp)}/8 fired\n")

    print("PARAMETER-FREE TARGETS (recomputed from d)")
    pf = [f"d%{m}" for m in RESIDUE_TARGET_MODS] + ["bit_mid","bit_top2","u_bin8",
          "q1_parity","q1_mod3","q2_parity","q2_mod3"]
    res = []
    for name in pf:
        z,p = eval_maxz(tg[name], flist, a.shuffles, rng); res.append(p)
        print(f"  {name:12s} maxz={z:8.2f}  p={p:.4f}  {'FIRES' if p<0.05 else 'null'}")
    # Bonferroni across the param-free family
    print(f"  family min-p={min(res):.4f}  Bonferroni x{len(pf)} = {min(min(res)*len(pf),1):.4f}\n")

    print("n/k CHANNEL (nmax search priced into the null)")
    z,p,best_nm = eval_nk_channel(ncurves, flist, a.shuffles, rng)
    print(f"  max over (feature x nmax): maxz={z:.2f}  best nmax={best_nm}  corrected p={p:.4f}  {'FIRES' if p<0.05 else 'null'}")

if __name__ == "__main__":
    main()
