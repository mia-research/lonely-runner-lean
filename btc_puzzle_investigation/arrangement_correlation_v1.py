#!/usr/bin/env python3
"""
arrangement_correlation_v1.py -- EXPLORATORY.  Targets the explicit SCOPE GAP of the
semicircle null: it bounds the |V| MARGINAL and says nothing about correlations that
leave every order statistic intact.

The right null for a pure ARRANGEMENT statistic is the class permutation (it preserves
the |V| multiset EXACTLY, so every order statistic is invariant and only arrangement is
destroyed) -- the mirror image of the semicircle null's power profile.

STATISTIC.  For an index map sigma on (Z/n)^*,  C(sigma) = corr( u(a), u(sigma(a)) ).

WHICH MAPS ARE INFORMATIVE, AND WHICH ARE FORCED -- stated before running:
  * TRANSLATIONS sigma(a) = a+b are FORCED and carry ZERO information.  The record's
    identity sum_a V(a) conj(V(a+b)) = n(n delta_b - 1) is curve-independent, and with
    V = 2i sqrt(p) u it reads sum_a u(a) u(a+b) = n(n delta_b - 1)/(4p).  Reported here
    ONLY as a DIAGNOSTIC: it must fire hugely against the class null (which destroys
    additive arrangement), demonstrating that this null is WRONG for additive maps.
    A fire on a+1 is the known identity, NOT a finding.
  * MULTIPLICATIVE TRANSLATIONS sigma(a) = lam*a are the Wiener-Khinchin dual of the
    multiplicative spectrum, already tested and null.  Included as a second diagnostic.
  * sigma(a) = a^{-1}, a^2, a^3 are NEITHER additive nor multiplicative translations, so
    neither forced identity applies and no spectrum is dual to them.  ***THESE ARE THE
    LIVE TESTS.***

Exact int index maps; float only in the correlation, ranked against null draws.
"""
import argparse, json, sys
import numpy as np
from sympy import primitive_root
from twist_orbit_spectrum_run_v1 import signal
from theta_structure_scan_v1 import u_sequence, class_perm_freq

LIVE = ["inv", "sq", "cube"]
DIAG = ["add1", "mul2"]


def sigma_map(name, n):
    a = np.arange(1, n, dtype=np.int64)
    if name == "add1":
        return a, (a + 1) % n
    if name == "mul2":
        return a, (2 * a) % n
    if name == "inv":
        return a, np.array([pow(int(t), n - 2, n) for t in a], dtype=np.int64)
    if name == "sq":
        return a, (a * a) % n
    if name == "cube":
        return a, (a * a % n * a) % n
    raise ValueError(name)


def corr(u, src, dst):
    x, y = u[src], u[dst]
    ok = (dst != 0)
    x, y = x[ok], y[ok]
    x = x - x.mean(); y = y - y.mean()
    d = np.sqrt((x * x).sum() * (y * y).sum())
    return float(x.dot(y) / d) if d > 0 else 0.0          # noqa: float


def run(p, R, rng):
    s = signal(p, 7)
    if s is None:
        return None
    n, c, X, Y = s
    u, V = u_sequence(p, n, c)
    maps = {m: sigma_map(m, n) for m in DIAG + LIVE}
    data = {m: corr(u, *maps[m]) for m in maps}
    nulls = {m: [] for m in maps}
    for _ in range(R):
        Vn = class_perm_freq(V, n, rng)
        un = (Vn / (2j * np.sqrt(p))).real                 # noqa: float
        for m in maps:
            nulls[m].append(corr(un, *maps[m]))
    o = {"p": p, "n": int(n)}
    print(f"p={p:5d} n={n:5d}")
    for m in DIAG + LIVE:
        arr = np.array(nulls[m])
        z = (data[m] - arr.mean()) / (arr.std() + 1e-15)   # noqa: float
        ge = int((np.abs(arr) >= abs(data[m])).sum())
        tag = "DIAG(forced)" if m in DIAG else "LIVE"
        o[m] = {"data": data[m], "null_mean": float(arr.mean()),
                "null_sd": float(arr.std()), "z": float(z),
                "ge_abs": ge, "R": R}
        print(f"   {m:6s} {tag:12s} C={data[m]:+.5f}  null {arr.mean():+.5f}"
              f"+-{arr.std():.5f}  z={z:+7.2f}  |null|>=|data|: {ge}/{R}")
    sys.stdout.flush()
    return o


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", type=int, nargs="+",
                    default=[823, 1303, 1831, 2251, 2731, 3271, 3691, 4159, 4831])
    ap.add_argument("-R", type=int, default=200)
    ap.add_argument("--seed", type=int, default=20260801)
    ap.add_argument("--out", default="arrangement_correlation_v1.json")
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    res = [r for r in (run(p, a.R, rng) for p in a.primes) if r]
    # pooled per map
    print("\n=== pooled over primes ===")
    for m in DIAG + LIVE:
        zs = np.array([r[m]["z"] for r in res])
        print(f"  {m:6s} mean z {zs.mean():+7.3f}  pooled z "
              f"{zs.mean()*np.sqrt(len(zs)):+7.2f}  signs "
              f"{int((zs>0).sum())}/{len(zs)}  max|z| {np.abs(zs).max():.2f}")
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"\nwrote {a.out}")


if __name__ == "__main__":
    main()
