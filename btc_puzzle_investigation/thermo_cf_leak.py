#!/usr/bin/env python3
"""
thermo_cf_leak.py  —  "thermodynamics on number theory", in the leak harness.

Operationalizes the docs' "temperature" as statistical mechanics on the continued-
fraction expansion of the key's position u = (d-2^{N-1})/2^{N-1}. The partial
quotients [a1,a2,...] of u are the "system": n is just the CF denominator, so this
is the same object the (n,k,D) decomposition lives on, viewed thermodynamically.

Observables (per key), all EXACT integer except entropy (float, then RANK-binned --
a monotone ranked transform, never a threshold on the data):
  L       = # partial quotients                 ("particle count")
  E       = sum a_i                             ("total energy")
  Emax    = max a_i                             ("largest level")
  Elog    = sum a_i.bit_length()                (sum log2 a_i, Lyapunov/Khinchin energy)
  Z2      = sum a_i^2                            (2nd-moment partition weight)
  H       = -sum p_i log2 p_i, p_i=a_i/sum a    (Boltzmann/Shannon entropy of occupations)
Continuous observables are quantile-binned to 8 classes by argsort RANK (exact
ordering, no float threshold) to serve as discrete targets.

Test = the SAME map-property leak test: does public (X,Y) predict a key's thermo
statistic? Estimator = Westfall-Young min-p over the (X,Y) feature family, integer
verdict (20*c<tot), positive+negative controls, base-key-imprint floor min_bits=40.

Usage: python3 thermo_cf_leak.py --data {real,synthetic} [--n N] [--shuffles R]
"""
import argparse, math, numpy as np, pandas as pd
from leak_test_exact import features as int_features, mi_bits, minp_pairs

def cf_pq(num, den):
    """Exact continued-fraction partial quotients of num/den (num<den => drop a0=0)."""
    a = []
    while den:
        q, num, den = num // den, den, num % den
        a.append(q)
    return a[1:] if a else []          # a[0]==0 since num<den; real PQs follow

def entropy_bits(a):
    """Shannon entropy of occupations a_i/sum a, in bits. Float -> rank-binned by caller."""
    s = sum(a)
    if s == 0 or len(a) <= 1:
        return 0                       # sentinel (rank-binned by caller)
    return -sum((x / s) * math.log2(x / s) for x in a if x > 0)      # noqa: float (ranked statistic only)

def qbin(vals, bins=8):
    """Quantile bin by argsort RANK (exact ordering; no float threshold touches data)."""
    v = np.asarray(vals)
    ranks = np.empty(len(v), dtype=int)
    ranks[np.argsort(v, kind="stable")] = np.arange(len(v))
    return (ranks * bins) // len(v)

def thermo_targets(d, N, rng):
    A = [cf_pq(int(v) - (1 << (int(n) - 1)), 1 << (int(n) - 1)) for v, n in zip(d, N)]
    A = [a if a else [1] for a in A]                 # guard empty (u==0), rare
    L    = np.array([len(a) for a in A])
    E    = [sum(a) for a in A]
    Emax = [max(a) for a in A]
    Elog = [sum(x.bit_length() for x in a) for a in A]
    Z2   = [sum(x * x for x in a) for a in A]
    H    = [entropy_bits(a) for a in A]              # noqa: float (rank-binned next)
    tg = {}
    tg["cf_len"]   = np.minimum(L, 12)               # integer target, capped
    tg["E_bin"]    = qbin(E)
    tg["Emax_bin"] = qbin(Emax)
    tg["Elog_bin"] = qbin(Elog)
    tg["Z2_bin"]   = qbin(Z2)
    tg["H_bin"]    = qbin(H)                          # entropy, rank-binned
    tg["E_par"]    = np.array([e & 1 for e in E])
    tg["Emax_par"] = np.array([e & 1 for e in Emax])
    return tg

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", choices=["real", "synthetic"], default="real")
    ap.add_argument("--n", type=int, default=20000)
    ap.add_argument("--shuffles", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=31337)
    ap.add_argument("--min-bits", type=int, default=40)   # base-key-imprint floor
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

    feats = list(int_features(X, Y).values())
    tg = thermo_targets(d, N, rng)
    # controls
    x7 = np.array([int(x) % 7 for x in X]); tg["POS_strong"] = x7.copy()
    keep = rng.random(len(X)) < 0.10                       # noqa: float (control build)
    tg["POS_f0.10"] = np.where(keep, x7, rng.integers(0, 7, len(X)))
    for j in range(8): tg[f"NEG_{j}"] = rng.integers(0, 2, len(X))

    def run(y): return minp_pairs([(f, y) for f in feats], a.shuffles, rng)
    def line(name, res):
        b, om, c, tot = res; fires = 20 * c < tot
        print(f"  {name:10s} obs_upper_count={om:5d}/{a.shuffles}  corr_p={c/tot:.4f}  {'FIRES' if fires else 'null'}")  # noqa: float

    print(f"# THERMO-CF leak test  data={a.data}  keys={len(df)}  min_bits={a.min_bits}  "
          f"features={len(feats)}  shuffles={a.shuffles}")
    print("CONTROLS")
    for nm in ["POS_strong", "POS_f0.10"]: line(nm, run(tg[nm]))
    negfire = sum(1 for j in range(8) if (lambda r: 20*r[2] < r[3])(run(tg[f"NEG_{j}"])))
    print(f"  NEGATIVE: {negfire}/8 fired")
    print("THERMODYNAMIC targets (CF partial-quotient system)")
    for nm in ["cf_len","E_bin","Emax_bin","Elog_bin","Z2_bin","H_bin","E_par","Emax_par"]:
        line(nm, run(tg[nm]))

if __name__ == "__main__":
    main()
