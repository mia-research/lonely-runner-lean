#!/usr/bin/env python3
"""
cubic_moment_power_v1.py — test A re-run on BOTH sets, with POWER quantified.

Fixes two errors in masked_structure_harness_v1.py's section A:
  (1) it tested only the 82 real keys (N=82) and a hand-rolled 9000-pt pool, ignoring
      the 36k full-range known-d set (constructed_keys_fullrange_v1.npz).  Standing
      rule: run every test on BOTH sets.
  (2) it reported "null" with no POWER statement.  A null at N=82 is near-vacuous
      unless we say what effect size it could have seen.

Statistic: S(set) = |E_set[z^3] - mu|^2, mu = population mean over the 36k curve points.
EXACT: z^3 in Z[omega] (integers), E as Fraction, S as Fraction, ranking by exact
Fraction comparison.  NO float in the signal path (the values are ~1e227 and the
earlier float version was one order of magnitude from overflowing a double).

Power: inject a controlled rotation-toward-a-direction perturbation of known size
into a random subset and find the smallest detectable effect at each N.
"""
import os, csv, random
from fractions import Fraction
import numpy as np
from int1_frame_operator_v1 import build_secp

HERE = os.path.dirname(os.path.abspath(__file__))


def emul(z, w):
    a, b = z; c, d = w
    return (a * c - b * d, a * d + b * c - b * d)


def ecube(z):
    return emul(emul(z, z), z)


def enorm_frac(a, b):
    return a * a - a * b + b * b


def load_82():
    d, x = [], []
    with open(os.path.join(HERE, "puzzles_verified.csv")) as f:
        for r in csv.DictReader(f):
            d.append(int(r["private_key"], 16))       # HEX (bug fixed)
            x.append(int(r["X"], 16))
    return d, x


def load_36k():
    z = np.load(os.path.join(HERE, "constructed_keys_fullrange_v1.npz"), allow_pickle=True)
    return [int(v) for v in z["d"]], [int(v) for v in z["X"]], [int(v) for v in z["N"]]


def stat_of(cubes, idx, mua, mub):
    n = len(idx)
    Sa = sum(cubes[i][0] for i in idx); Sb = sum(cubes[i][1] for i in idx)
    return enorm_frac(Fraction(Sa, n) - mua, Fraction(Sb, n) - mub)   # exact Fraction


def main():
    eis, _ = build_secp()
    rng = random.Random(11)

    print("Loading 36k full-range known-d set + the 82 real keys ...")
    d36, x36, bits36 = load_36k()
    d82, x82 = load_82()
    print(f"  36k set: N={len(x36)}  (bitlen bulk={max(set(bits36), key=bits36.count)})")
    print(f"  real   : N={len(x82)}")

    print("Computing exact z^3 for the 36k pool ...")
    cub36 = [ecube(eis(x)) for x in x36]
    M = len(cub36)
    mua = Fraction(sum(c[0] for c in cub36), M)      # population baseline mu
    mub = Fraction(sum(c[1] for c in cub36), M)
    cub82 = [ecube(eis(x)) for x in x82]

    # ---------------------------------------------------------------- null by N
    print("\nNull distribution of S = |E[z^3]-mu|^2 vs N (exact; 400 draws each):")
    print(f"  {'N':>7} {'median S':>12} {'95th pct S':>12}   (S scales ~ 1/N as expected)")
    null_by_N = {}
    for n in (82, 500, 2000, 10000, 36000):
        draws = sorted(stat_of(cub36, rng.choices(range(M), k=n), mua, mub) for _ in range(400))
        null_by_N[n] = draws
        med = draws[200]; p95 = draws[380]
        print(f"  {n:>7} {float(med):>12.3e} {float(p95):>12.3e}")

    def verdict(name, cubes, idx, n=None):
        idx = list(idx); n = n or len(idx)
        S = stat_of(cubes, idx, mua, mub)
        draws = null_by_N.get(n) or sorted(
            stat_of(cub36, rng.choices(range(M), k=n), mua, mub) for _ in range(400))
        rank = sum(1 for t in draws if t <= S) / len(draws)      # exact comparison
        flag = "ANOMALY" if (rank < 0.025 or rank > 0.975) else "null"
        print(f"  {name:28} N={n:>6}  S={float(S):>10.3e}  rank-pct={rank:.3f}  => {flag}")
        return rank

    print("\nSET tests (null = random subsets of the 36k known-d curve points):")
    verdict("[ctrl] random-82 (held out)", cub36, rng.sample(range(M), 82), 82)
    verdict("[ctrl] random-2000", cub36, rng.sample(range(M), 2000), 2000)
    verdict("82 REAL solved keys", cub82, range(82), 82)
    verdict("36k constructed (whole set)", cub36, range(M), 36000)

    # 36k restricted to >=240-bit (matched to nothing in particular; power demo)
    hi = [i for i, b in enumerate(bits36) if b >= 240]
    verdict("36k subset bitlen>=240", cub36, hi, len(hi))

    # ---------------------------------------------------------------- POWER
    # Inject: replace a fraction f of a random N-subset with points whose z^3 is
    # rotated to a common direction (the strongest possible coherent effect).
    print("\nPOWER: smallest injected coherent fraction f detected at 95% of the null,")
    print("       f = fraction of the set replaced by cubes aligned to one direction.")
    print("       (this is the MOST detectable effect of its size; real effects need more)")
    print(f"  {'N':>7}  {'min detectable f':>17}  {'~equivalent bits of set':>24}")
    for n in (82, 500, 2000, 10000, 36000):
        thresh = null_by_N[n][380]                      # 95th pct of null
        found = None
        for f in (0.005, 0.01, 0.02, 0.05, 0.10, 0.20, 0.35, 0.50, 0.75, 1.0):
            hits = 0
            for _ in range(60):
                idx = rng.choices(range(M), k=n)
                cs = [cub36[i] for i in idx]
                k = int(round(f * n))
                if k:
                    # align k cubes to the direction of a fixed reference cube
                    ref = cub36[0]
                    scale = 1
                    cs[:k] = [(ref[0] * scale, ref[1] * scale)] * k
                Sa = sum(c[0] for c in cs); Sb = sum(c[1] for c in cs)
                S = enorm_frac(Fraction(Sa, n) - mua, Fraction(Sb, n) - mub)
                if S > thresh: hits += 1
            if hits >= 48:                              # 80% power
                found = f; break
        print(f"  {n:>7}  {str(found) if found else '>1.0':>17}  "
              f"{'~' + str(int(round((found or 1) * n))) + ' points':>24}")

    print("\nNOTE: the 36k set is OUR keys with known d -> for THIS statistic it is a")
    print("      full-power CONTROL/null, not a rival hypothesis.  Its value here is")
    print("      (a) a proper 36000-point null pool, (b) the power calibration above,")
    print("      which is what makes the N=82 result interpretable at all.")


if __name__ == "__main__":
    main()
