#!/usr/bin/env python3
"""
pointed_kn.py  —  targeted (frozen-k / frozen-n) datasets + the leak test on them.

Idea (user, 2026-07-07): the puzzle keys are random small integers on secp256k1, so
synthetic keys are as valid a testbed. Build POINTED data that isolates one axis of
the (n,k) decomposition:
  * FROZEN-k:  fix k=k0, sweep n over its coprime range (fixed N) -> all variation is
    in n. Cleanest possible "does (X,Y) leak n?" (no k confound, max power on n).
  * FROZEN-n:  fix n=n0, sweep k coprime to n0 -> cleanest "does (X,Y) leak k?".
Then vary N, and expand the frozen value to a few low / high / consecutive.

Construction uses RANDOM residual D (draw d from the Farey cell of (n,k), reject to
the exact cell) -- NEVER d=base(n,k) (the D==0 base-key trap, hunt_method). X,Y=d*G by
exact integer EC arithmetic; best_nk(d) is re-verified == (n,k) on every kept key.

Test = the same map-property harness (WY min-p over the (X,Y) feature family, integer
verdict, positive+negative controls). Targets are the FREE axis (n for frozen-k, k for
frozen-n) as value(rank-binned), residues, and parity.

Exact integer signal path; float only inside mi_bits (ranked) and the display string.

Usage: python3 pointed_kn.py [--per 25] [--bits 64] [--shuffles 2000]
"""
import argparse, math, numpy as np
from math import gcd
from exact_core import best_nk
from farm.lib_data import ec_mul, G, N_ORD
from leak_test_exact import features as int_features, mi_bits, minp_pairs

def cell_key(n, k, N, rng, max_try=4000):
    """Draw d in [2^{N-1},2^N) with best_nk(d,N,256)==(n,k) and RANDOM D (not base)."""
    lo = 1 << (N - 1)
    base = lo + (lo * k) // n
    W = max(4, lo // (n * n))                 # cell half-width ~ D-floor
    for _ in range(max_try):
        d = base + int(rng.integers(-W, W + 1))
        if lo <= d < 2 * lo and best_nk(d, N, 256) == (n, k):
            return d
    return None

def build(frozen, val, N, others, per, rng):
    """frozen='k' fixes k=val and sweeps n in `others`; frozen='n' fixes n=val, sweeps k."""
    d, freeaxis = [], []
    for o in others:
        n, k = (o, val) if frozen == "k" else (val, o)
        if gcd(k, n) != 1 or not (0 < k < n) or n > 256:
            continue
        got = 0
        for _ in range(per * 3):
            if got >= per: break
            dd = cell_key(n, k, N, rng)
            if dd is None: continue
            d.append(dd); freeaxis.append(n if frozen == "k" else k); got += 1
    X, Y = [], []
    for dd in d:
        P = ec_mul(dd % N_ORD, G); X.append(P[0]); Y.append(P[1])
    # correctness gate
    ok = sum(1 for dd, fa in zip(d[:20], freeaxis[:20])
             if best_nk(dd, N, 256) == ((fa, val) if frozen == "k" else (val, fa)))
    assert ok == min(20, len(d)), f"cell identity failed {ok}"
    return np.array(d, dtype=object), np.array(freeaxis), X, Y

def qbin(vals, bins=8):
    v = np.asarray(vals); r = np.empty(len(v), dtype=int)
    r[np.argsort(v, kind="stable")] = np.arange(len(v))
    return (r * bins) // len(v)

def test(tag, freeaxis, X, Y, shuffles, rng):
    feats = list(int_features(X, Y).values())
    tg = {"free_bin": qbin(freeaxis), "free_par": freeaxis & 1,
          "free_m3": freeaxis % 3, "free_m5": freeaxis % 5}
    x7 = np.array([int(x) % 7 for x in X]); tg["POS_strong"] = x7
    keep = rng.random(len(X)) < 0.10                          # noqa: float (control build)
    tg["POS_f0.10"] = np.where(keep, x7, rng.integers(0, 7, len(X)))
    for j in range(6): tg[f"NEG_{j}"] = rng.integers(0, 2, len(X))
    def run(y):
        b, om, c, tot = minp_pairs([(f, y) for f in feats], shuffles, rng); return c, tot, om
    def line(nm):
        c, tot, om = run(tg[nm]); print(f"  {nm:11s} corr_p={c/tot:.4f}  {'FIRES' if 20*c<tot else 'null'}  (obs_upper={om}/{shuffles})")  # noqa: float
    nf = sum(1 for j in range(6) if (lambda r: 20*r[0] < r[1])(run(tg[f"NEG_{j}"])))
    print(f"# {tag}  keys={len(X)}  features={len(feats)}  distinct_free={len(set(freeaxis.tolist()))}")
    print(f"  CONTROLS: POS_strong / POS_f0.10 below; NEGATIVE {nf}/6 fired")
    for nm in ["POS_strong", "POS_f0.10", "free_bin", "free_par", "free_m3", "free_m5"]:
        line(nm)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--per", type=int, default=25)
    ap.add_argument("--bits", type=int, default=64)
    ap.add_argument("--shuffles", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=31337)
    a = ap.parse_args(); rng = np.random.default_rng(a.seed)
    N = a.bits
    print(f"=== POINTED (n,k) leak tests  N={N}  per={a.per} ===\n")
    # FROZEN-k: a low, a high, and consecutive frozen k; sweep n over coprime range
    for k0 in [1, 2, 7, 200]:
        others = [n for n in range(k0 + 1, 257) if gcd(n, k0) == 1]
        d, fa, X, Y = build("k", k0, N, others, a.per, rng)
        print(f"--- FROZEN k={k0}: target = n (the free axis) ---")
        test(f"frozen-k={k0} N={N}", fa, X, Y, a.shuffles, rng); print()
    # FROZEN-n: prime n0 (max coprime k); sweep k
    for n0 in [199, 251]:
        others = [k for k in range(1, n0) if gcd(k, n0) == 1]
        d, fa, X, Y = build("n", n0, N, others, a.per, rng)
        print(f"--- FROZEN n={n0}: target = k (the free axis) ---")
        test(f"frozen-n={n0} N={N}", fa, X, Y, a.shuffles, rng); print()

if __name__ == "__main__":
    main()
