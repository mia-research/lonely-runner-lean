#!/usr/bin/env python3
"""
Recompute the (n,k,D,D_terms) decomposition EXACTLY (exact_core) for both the real
and synthetic key sets, diff against the float-era CSV columns, and write *_exact.csv.
Keys (d,X,Y) are unchanged (already exact); only derived columns are rebuilt.
"""
import pandas as pd, numpy as np
from exact_core import best_nk, residual, d_terms, cf_denoms

def redo(df, dcol, ncol, kcol):
    d = [int(x) for x in df[dcol]]; N = [int(b) for b in df["bits"]]
    n_e, k_e, D_e, T_e, q1, q2 = [], [], [], [], [], []
    for di, Ni in zip(d, N):
        n, k = best_nk(di, Ni, 256)
        n_e.append(n); k_e.append(k)
        D_e.append(residual(di, Ni, n, k)); T_e.append(d_terms(di, Ni, n, k))
        qs = cf_denoms(di, Ni); q1.append(qs[0]); q2.append(qs[1] if len(qs) > 1 else qs[0])
    out = df.copy()
    out["n_exact"], out["k_exact"] = n_e, k_e
    out["D_exact"], out["Dterms_exact"] = D_e, T_e
    out["q1_exact"], out["q2_exact"] = q1, q2
    nchg = int(np.sum(np.array(n_e) != df[ncol].to_numpy()))
    kchg = int(np.sum(np.array(k_e) != df[kcol].to_numpy()))
    # bit-lengths where n changed
    chg_bits = sorted(set(int(b) for b, a, e in zip(N, df[ncol], n_e) if a != e))
    return out, nchg, kchg, chg_bits

print("=== REAL (btc_puzzle_master.csv) ===")
r = pd.read_csv("btc_puzzle_master.csv"); r = r[r.status == "SOLVED"].reset_index(drop=True)
ro, nchg, kchg, cb = redo(r, "priv_dec", "n", "k")
print(f"  keys={len(ro)}  n changed vs float: {nchg}   k changed: {kchg}   changed-bit-lengths: {cb}")
ro.to_csv("btc_puzzle_master_exact.csv", index=False)

print("=== SYNTHETIC (constructed_keys_1to160_100k.csv) ===")
s = pd.read_csv("constructed_keys_1to160_100k.csv", dtype={"d": str})
so, nchg, kchg, cb = redo(s, "d", "n", "k")
print(f"  keys={len(so)}  n changed vs float: {nchg}   k changed: {kchg}")
print(f"  changed-bit-length range: {(min(cb),max(cb)) if cb else None}  count-of-distinct-N: {len(cb)}")
so.to_csv("constructed_keys_1to160_100k_exact.csv", index=False)
print("wrote *_exact.csv for both")
