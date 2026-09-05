#!/usr/bin/env python3
"""
power_scaling.py  —  telling a noise-level SIGNAL from NOISE by how it scales with N.

Problem (user, 2026-07-07): if a leak sits near the noise floor, a single p-value
can't separate it from a false positive. But signal and noise scale DIFFERENTLY with
sample size, and that is an invariant you can measure:

  * bias-corrected MI  I_c(N) = I_raw(N) - mean(permutation-null MI at N)
      SIGNAL : I_c(N) -> the true MI (a positive PLATEAU); log-log slope ~ 0
      NOISE  : I_c(N) -> 0, decaying ~1/N;                 log-log slope ~ -1
  * permutation z(N) = (I_raw - mean_null) / std_null
      SIGNAL : grows ~ sqrt(N)   (slope > 0 vs sqrt(N))
      NOISE  : stays O(1), no trend

So: run the SAME statistic at increasing N and fit the scaling. This classifies a
candidate no single run can. Reference curves below: pure noise (f=0), and planted
leaks at f=2%/5% of labels (a deliberately faint, noise-level signal) through the
X%7 channel -- so you can watch the signal curve separate from the noise curve.

MI is the ranked-float statistic (sanctioned); z is a reported diagnostic, never a
data threshold. Integer everywhere else.

Usage: python3 power_scaling.py [--Bnull 400]
"""
import argparse, numpy as np, pandas as pd
from leak_test_exact import mi_bits

NS = [500, 1000, 2000, 5000, 10000, 20000, 40000]

def scaling(feat, target_fn, Ns, Bnull, rng):
    """target_fn(n, rng) -> integer target array of length n. Returns per-N (I_c, z)."""
    out = []
    for n in Ns:
        f = feat[:n]
        y = target_fn(n, rng)
        raw = mi_bits(f, y)
        nulls = np.array([mi_bits(f, y[rng.permutation(n)]) for _ in range(Bnull)])  # noqa: float
        mu = nulls.mean(); sd = nulls.std() + 1e-12                                   # noqa: float
        out.append((n, raw - mu, (raw - mu) / sd))                                    # noqa: float
    return out

def loglog_slope(ns, ys):
    """Slope of log|y| vs log n (least squares). ~0 => plateau (signal), ~-1 => 1/N (noise)."""
    x = np.log(np.array(ns, float)); v = np.abs(np.array(ys, float)) + 1e-15          # noqa: float
    ly = np.log(v)                                                                    # noqa: float
    return float(np.polyfit(x, ly, 1)[0])                                             # noqa: float

def z_sqrtN_slope(ns, zs):
    x = np.sqrt(np.array(ns, float))                                                  # noqa: float
    return float(np.polyfit(x, np.array(zs, float), 1)[0])                            # noqa: float

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--Bnull", type=int, default=400)
    ap.add_argument("--seed", type=int, default=31337)
    a = ap.parse_args(); rng = np.random.default_rng(a.seed)
    df = pd.read_csv("constructed_keys_1to160_100k_exact.csv", dtype={"d": str}, low_memory=False)
    df = df[df.bits >= 40].reset_index(drop=True)
    if len(df) < max(NS):
        df = pd.concat([df] * (max(NS) // len(df) + 1), ignore_index=True)
    x7 = np.array([int(x, 16) % 7 for x in df["X"][:max(NS)]], dtype=np.int64)  # channel carrying the plant

    def planted(f):
        def fn(n, rng):
            base = x7[:n]
            keep = rng.random(n) < f              # noqa: float (target construction)
            return np.where(keep, base, rng.integers(0, 7, n))
        return fn

    print(f"# POWER-SCALING discriminator  channel=X%7  Bnull={a.Bnull}")
    print(f"# columns: N -> (I_c bits = bias-corrected MI, z = permutation z)\n")
    cases = [("NOISE   f=0.00", planted(0.0)), ("PLANT   f=0.02", planted(0.02)),   # noqa: float (plant strengths)
             ("PLANT   f=0.05", planted(0.05)), ("STRONG  f=0.30", planted(0.30))]  # noqa: float (plant strengths)
    hdr = "  case            " + "".join(f"{n:>12d}" for n in NS)
    for label, fn in cases:
        res = scaling(x7, fn, NS, a.Bnull, rng)
        Ic = [r[1] for r in res]; z = [r[2] for r in res]
        s_mi = loglog_slope(NS, Ic); s_z = z_sqrtN_slope(NS, z)
        verdict = "SIGNAL" if (s_mi > -0.5 and s_z > 0) else "noise"   # noqa: float (slope classifier, not a data threshold)
        print(f"[{label}]")
        print("   I_c :" + "".join(f"{v:12.5f}" for v in Ic))
        print("   z   :" + "".join(f"{v:12.2f}" for v in z))
        print(f"   -> loglog-slope(I_c)={s_mi:+.2f} (0=plateau,-1=1/N)   "
              f"z-vs-sqrtN slope={s_z:+.4f}   => {verdict}\n")
    print("Classifier: I_c log-log slope ~0 AND z rising with sqrt(N) => SIGNAL;")
    print("            I_c slope ~ -1 AND z flat/no trend             => NOISE.")

if __name__ == "__main__":
    main()
