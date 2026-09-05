#!/usr/bin/env python3
"""
coherent_pool_p0prime_stageC_run_v1.py -- Stage C, the FROZEN firing decision of
PREREG_coherent_pool_P0prime_v1.md: the held-out stratum S monolithic A0 pool.

Reads the FROZEN S freq-list (SHA verified against the value recorded at setup
time, BEFORE this pool is computed), recomputes exact-integer q_p on each held-out
prime, and pools under A0 = monolithic (s_p = +1) against the exact 2^k
sign-permutation null.  Also reports the leave-991 pool (991 overlaps the
discovery set -> not truly OOS; a prereg-partition defect caught at execution).

Exact integers in the decision path; the pre-existing row-budget FFT float is the
sanctioned carve-out.  check_no_float.py passes.
"""
import argparse, hashlib
import numpy as np
from sympy import primitive_root
from row_budget_run_v1 import mu6_orbits, Permuter, nlow_batch
from row_budget_core_v1 import curve_orbit
from coherent_pool_p0prime_v1 import exact_pool_pvalue

FROZEN_SHA = "dcac39bd65b41014b289692f78b1bfd5adc351ae7cadacff93b6bd57fa71c013"
DISCOVERY = {163, 211, 349, 433, 577, 991, 2089, 4159, 9319, 19231}


def load_S(path):
    raw = open(path, "rb").read()
    sha = hashlib.sha256(raw).hexdigest()
    assert sha == FROZEN_SHA, f"S FREQ HASH MISMATCH {sha}"
    params = {}          # p -> (n, beta, lam)
    freqs = {}           # p -> [(b,c), ...]
    for line in raw.decode().splitlines():
        if line.startswith("#"):
            if line.startswith("# p="):
                d = dict(tok.split("=") for tok in line[2:].split() if "=" in tok)
                p = int(d["p"]); params[p] = (int(d["n"]), int(d["beta"]), int(d["lam"]))
            continue
        if not line.strip():
            continue
        p, b, c = (int(t) for t in line.split())
        freqs.setdefault(p, []).append((b, c))
    return params, freqs, sha


def q_for_prime(p, n, beta, lam, F, R, rng):
    X, Y, nn = curve_orbit(p)
    assert nn == n
    # revalidate the frozen curve params (C-EQ-int == 0) at run time
    idx = (lam * np.arange(n)) % n
    assert int(np.max((X[idx] - beta * X) % p)) == 0, f"C-EQ-int != 0 at p={p}"
    reps6, orb6, unit6, pw6 = mu6_orbits(n, lam)
    P6 = Permuter(n, reps6, orb6, unit6, pw6)
    tab = np.exp(2j * np.pi * np.arange(p) / p)                # noqa: float (carve-out)
    char_total = 0; null_total = 0
    for (b, c) in F:
        e = (b * X + c * Y) % p                                # exact integer exponent
        s = tab[e]; s[0] = 0.0                                 # noqa: float (carve-out)
        rows = [s] + [s[P6.draw(rng)] for _ in range(R)]
        NL, _, _ = nlow_batch(np.array(rows), n)
        char_total += int(NL[0]); null_total += int(NL[1:1 + R].sum())
    return R * char_total - null_total


def report_pool(tag, ps, qs):
    s = [1] * len(qs)
    num, den, W, k = exact_pool_pvalue(qs, s)
    aligned = sum(1 for q in qs if q > 0)
    print(f"  [{tag}] k={k}  aligned(+)={aligned}/{len(qs)}  W={W:+d}  "
          f"p = {num}/{den} ~ {num/den:.4g}")                  # noqa: float (display)
    return num, den, aligned, len(qs)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--freqs", default="coherent_pool_p0prime_stageC_S_FREQS.txt")
    ap.add_argument("--R", type=int, default=64)
    ap.add_argument("--seed", type=int, default=20260826)
    a = ap.parse_args()
    params, freqs, sha = load_S(a.freqs)
    print(f"FROZEN S freq-list verified  SHA {sha[:16]}...  R={a.R} seed={a.seed}")
    rng = np.random.default_rng(a.seed)
    import time

    rows = []
    for p in sorted(params):
        n, beta, lam = params[p]
        t0 = time.time()
        q = q_for_prime(p, n, beta, lam, freqs[p], a.R, rng)
        rows.append((p, n, len(freqs[p]), q))
        seen = " (SEEN in discovery!)" if p in DISCOVERY else ""
        print(f"  p={p:>5} n={n:>5} m={len(freqs[p]):>6}  q={q:>+12}  "
              f"sign={'+' if q>0 else '-' if q<0 else '0'}  [{int(time.time()-t0)}s]{seen}")

    ps = [r[0] for r in rows]; qs = [r[3] for r in rows]
    print("\n=== HELD-OUT A0 (monolithic) firing decision — stratum S ===")
    report_pool("FROZEN-12 (as pre-committed)", ps, qs)
    keep = [(p, q) for p, q in zip(ps, qs) if p not in DISCOVERY]
    report_pool("leave-991 (genuinely OOS)", [p for p, _ in keep], [q for _, q in keep])
    jmax = max(range(len(qs)), key=lambda i: abs(qs[i]))
    report_pool(f"leave-one-out (drop max |q|, p={ps[jmax]})",
                [ps[i] for i in range(len(ps)) if i != jmax],
                [qs[i] for i in range(len(qs)) if i != jmax])
    print("\n  (Direction: q_p>0 == real curve has MORE low-tail modes than the "
          "mu6 null.  NOT a closure, NOT a leakage claim; anomaly drill continues.)")


if __name__ == "__main__":
    main()
