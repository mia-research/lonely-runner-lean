#!/usr/bin/env python3
"""
resonance_curve_demo.py  —  the phi(n)/n "resonance", made EXACT and curve-aligned.

The docs' "resonance via phi(n)" / "2-torus alignment", de-metaphored: n is chosen
so d ~ base(n,k) = 2^{N-1}(1 + k/n). Hence
    n*d = 2^{N-1}(n+k) + n*D          (exact integer identity, D = d - base)
so on the curve, with Q = 2^{N-1}*G,
    [n]P = (n+k)*Q + (n*D)*G .
The "resonance" = [n]P lands NEAR the coarse sublattice <Q>, offset by the residual
point (n*D)*G. This is real, not a metaphor. Two questions decide whether it leaks:

 (1) EXISTENCE (uses d): verify the identity; measure the residual d-log |n*D|.
     |n*D| is the exact quantity that would have to be SMALL to exploit it
     (baby-step/lattice reachable, say < 2^40). Predicted ~2^{N-9}.
 (2) PUBLIC DETECTABILITY (no d, attack-valid): sweep candidate m, form the POINT
     [m]P by successive addition, take a public statistic S(x([m]P)); is true-n's
     value systematically EXTREME among the 256 candidates? (KS of normalized rank
     vs Uniform, with an injected-outlier positive control.) This is WP6's
     candidate sweep but with the GROUP operation instead of an integer reduction.

Exact integer arithmetic throughout; the only float is the KS statistic / p, each
ranked or compared as a bounded readout (no float decides the existence identity).

Usage: python3 resonance_curve_demo.py [--keys K] [--mmax M]
"""
import argparse, numpy as np, pandas as pd
from exact_core import best_nk, residual
from farm.lib_data import ec_mul as _mul, ec_add as _add, G as _G, N_ORD

def existence(df):
    print("## (1) EXISTENCE — identity [n]P=(n+k)Q+(n*D)G, residual d-log |n*D|")
    rows = []
    for _, r in df.iterrows():
        N = int(r.bits); d = int(r.d); X = int(r.X, 16); Y = int(r.Y, 16)
        n, k = best_nk(d, N, 256)
        Q = _mul((1 << (N - 1)) % N_ORD, _G)
        # exact residual scalar: [n]d - (n+k)*2^{N-1}  (= n*D - r, r=(2^{N-1}k) mod n)
        res_scalar = n * d - (1 << (N - 1)) * (n + k)
        lhs = _mul(n % N_ORD, (X, Y))
        rhs = _add(_mul((n + k) % N_ORD, Q), _mul(res_scalar % N_ORD, _G))
        ok = (lhs == rhs)
        rows.append((N, abs(res_scalar).bit_length(), (N - 9), ok))
    okall = all(o for *_, o in rows)
    print(f"   identity holds on all {len(rows)} keys: {okall}")
    print(f"   {'N':>4} {'bits|n*D|':>9} {'~N-9':>5}  (residual d-log size = the exploitability gap)")
    for N, b, pred, ok in rows[:6] + rows[-4:]:
        print(f"   {N:>4} {b:>9} {pred:>5}")
    small = sum(1 for _, b, *_ in rows if b < 40)
    print(f"   keys with |n*D| < 2^40 (baby-step reachable): {small}/{len(rows)}")

def detect(df, mmax, shuffles, rng):
    print(f"\n## (2) PUBLIC DETECTABILITY — candidate sweep on the POINT [m]P, m=1..{mmax}")
    # per key: v[m-1] = x([m]P) mod 2^32 ; readout = normalized rank of true-n's value
    ranks_true = []; ranks_ctrl = []
    for _, r in df.iterrows():
        N = int(r.bits); d = int(r.d); X = int(r.X, 16); Y = int(r.Y, 16)
        n, _ = best_nk(d, N, 256)
        if n < 2 or n > mmax:
            continue
        P = (X, Y); acc = P; v = []
        for m in range(1, mmax + 1):
            v.append(acc[0] & 0xFFFFFFFF)          # public statistic of the point
            acc = _add(acc, P)                      # (m+1)P = mP + P
        v = np.array(v)
        s_true = v[n - 1]
        rank = (v < s_true).sum() + 0.5 * (v == s_true).sum()   # noqa: float (rank readout)
        ranks_true.append(rank / mmax)                          # noqa: float
        # positive control: inject an outlier at true-n for this key
        vc = v.copy(); vc[n - 1] = v.max() + 1
        s_c = vc[n - 1]
        rc = (vc < s_c).sum() + 0.5 * (vc == s_c).sum()          # noqa: float
        ranks_ctrl.append(rc / mmax)                             # noqa: float
    rt = np.array(ranks_true); rc = np.array(ranks_ctrl)
    from scipy.stats import kstest
    def ks_stat(a):
        return float(kstest(a, "uniform").statistic)          # noqa: float (ranked statistic only)
    def perm_p(obs, m, B):
        """Integer p: rank obs KS vs B matched nulls (true-n = a uniform-random candidate)."""
        ge = sum(1 for _ in range(B) if ks_stat(rng.integers(1, m + 1, len(rt)) / m) >= obs)  # noqa: float
        return ge, B
    ks_t = ks_stat(rt); ks_c = ks_stat(rc)
    gt, B = perm_p(ks_t, mmax, 2000); gc, _ = perm_p(ks_c, mmax, 2000)
    fires_t = 20 * (gt + 1) < (B + 1)      # corr_p < 0.05, integer-decided
    fires_c = 20 * (gc + 1) < (B + 1)
    print(f"   keys used (2<=n<={mmax}): {len(rt)}")
    print(f"   TRUE-n rank vs Uniform:  KS={ks_t:.3f}  perm_count={gt}/{B}  mean_rank={rt.mean():.3f}  "
          f"{'EXTREME (leak)' if fires_t else 'uniform (no public distinguisher)'}")
    print(f"   CONTROL (outlier@true-n): KS={ks_c:.3f}  perm_count={gc}/{B}  mean_rank={rc.mean():.3f}  "
          f"{'fires (powered)' if fires_c else 'DID NOT FIRE (void)'}")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--keys", type=int, default=400)
    ap.add_argument("--mmax", type=int, default=256)
    ap.add_argument("--shuffles", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=31337)
    a = ap.parse_args(); rng = np.random.default_rng(a.seed)
    real = pd.read_csv("btc_puzzle_master_exact.csv")
    real = real[real.status == "SOLVED"].rename(columns={"priv_dec":"d","X_hex":"X","Y_hex":"Y"})
    real = real[real.bits >= 26][["bits","d","X","Y"]].reset_index(drop=True); real["d"] = real["d"].astype(str)
    existence(real)
    # detectability: real keys + synthetic top-up for power
    syn = pd.read_csv("constructed_keys_1to160_100k_exact.csv", dtype={"d": str}, low_memory=False)
    syn = syn[syn.bits >= 26].rename(columns={"X_hex":"X","Y_hex":"Y"})[["bits","d","X","Y"]]
    syn = syn.sample(min(a.keys, len(syn)), random_state=a.seed).reset_index(drop=True)
    detect(pd.concat([real, syn], ignore_index=True), a.mmax, a.shuffles, rng)

if __name__ == "__main__":
    main()
