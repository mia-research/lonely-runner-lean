#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
brick_e_analysis_v2.py — FAST analysis layer for the powered Brick E rung, per PREREG v2 §§3-5.
Same statistic and decision as brick_e_analysis_v1.py; only the degree ENGINE is replaced.

v1 climbed D=0..N-1 with a Gaussian-elimination fit at each D -> O(N^4) per fit -> infeasible at
N=273 (p=547) x 2000 null draws. v2 reads the interpolant degree from NEWTON DIVIDED DIFFERENCES:
O(N^2) per fit, with the inverse denominators precomputed ONCE (the domain Q is fixed across draws).
The interpolant through distinct nodes is unique, so its degree == v1's min_degree_fit D (validated on
p=43: D_obs=14). Exact integer arithmetic; the only floats are reported percentiles.

Input: brick_e_rung_<p>_v2_data.json (or _data.json). Fits over the single large prime factor q=M
(the PH runner already reduced to the Sylow-qmax subgroup, so M in the JSON is the prime q, q>=n).
"""
import json, random, sys, math

def build_inv(ds, q):
    N = len(ds)
    inv = [[0] * N for _ in range(N)]
    for j in range(1, N):
        for i in range(j, N):
            inv[j][i] = pow((ds[i] - ds[i - j]) % q, q - 2, q)
    return inv

def newton_coef(cs, inv, q):
    N = len(cs); coef = [c % q for c in cs]
    for j in range(1, N):
        for i in range(N - 1, j - 1, -1):
            coef[i] = (coef[i] - coef[i - 1]) * inv[j][i] % q
    return coef

def newton_degree(cs, inv, q):
    coef = newton_coef(cs, inv, q)
    for k in range(len(coef) - 1, -1, -1):
        if coef[k] % q != 0:
            return k
    return 0

def newton_eval(coef, ds, x, q):        # value of the Newton interpolant at x
    N = len(coef); val = coef[N - 1] % q
    for k in range(N - 2, -1, -1):
        val = (val * (x - ds[k]) + coef[k]) % q
    return val

def analyze(fn, NDRAWS=2000):
    D = json.load(open(fn))
    p, n, q = D["p"], D["n"], D["M"]         # M is the single large prime (PH subgroup)
    lam, kappa = D["lam"], D["kappa"]
    cptab = {int(d): int(e) for d, e in D["cplus"].items()}
    Q = sorted(cptab)
    assert len(set(d % q for d in Q)) == len(Q), f"domain not distinct mod q={q} (ill-posed rung)"
    # kappa_eff (covariance globality on invertible values)
    ratios = set()
    for d in Q:
        d2 = (lam * d) % n
        if d2 in cptab and math.gcd(cptab[d], q) == 1:
            ratios.add(cptab[d2] * pow(cptab[d], -1, q) % q)
    assert len(ratios) == 1, f"kappa not global: {ratios}"
    keff = ratios.pop()
    # orbits + reps
    seen = set(); reps = []
    for d in Q:
        if d in seen: continue
        reps.append(d); x = lam * d % n
        while x != d: seen.add(x); x = lam * x % n
        seen.add(d)
    print(f" p={p} n={n} q={q} |Q|={len(Q)} reps={len(reps)} keff={keff} (sigma-kappa {kappa})", flush=True)

    kinv = pow(keff, -1, q)
    def propagate(repvals):
        tab = {}
        for d in Q:
            x = d; j = 0
            while x not in repvals:
                x = lam * x % n; j += 1
                assert j < 3
            tab[d] = repvals[x] * pow(kinv, j, q) % q
        return tab
    real_reps = {r: cptab[r] for r in reps}
    assert propagate(real_reps) == {d: cptab[d] % q for d in Q}, "covariance reproduction failed"

    ds = Q
    inv = build_inv(ds, q)                    # precompute ONCE
    cs_real = [cptab[d] % q for d in ds]
    Dobs = newton_degree(cs_real, inv, q)

    random.seed(20260820 + p)
    hist = []
    for _ in range(NDRAWS):
        rv = {r: random.randrange(q) for r in reps}
        tab = propagate(rv)
        hist.append(newton_degree([tab[d] for d in ds], inv, q))
    hist.sort()
    def pctile(dv):                           # pi = Pr_null(D <= dv); LOW pi = low-degree signal
        cnt = sum(1 for h in hist if h <= dv)
        return (cnt + 1) / (NDRAWS + 1)
    pi_obs = pctile(Dobs)

    # control (ii): exactly-covariant monomial a*d^i0 on Q if it exists, else plain deg-2 plant
    i0 = None
    for i in range(1, 4 * n):
        if all(pow((lam * d) % n, i, q) == keff * pow(d, i, q) % q for d in Q):
            i0 = i; break
    if i0 is not None:
        plant = [pow(d, i0, q) for d in ds]; note = f"exactly-covariant monomial i0={i0}"
    else:
        plant = [(77 * d * d + 123) % q for d in ds]; note = "plain deg-2 plant (no covariant monomial)"
    Dplant = newton_degree(plant, inv, q); pi_plant = pctile(Dplant)
    fired_ii = (sum(1 for h in hist if h <= Dplant) + 1) * 100 <= (NDRAWS + 1)   # pi_plant <= 0.01, integer

    # control (iii): calibration — the null degrees' own percentiles (uniformity)
    cal_low_cnt = sum(1 for h in hist if (sum(1 for g in hist if g <= h) + 1) * 100 <= (NDRAWS + 1))
    distinct_degs = sorted(set(hist))

    # INV: does the real interpolant invert uniquely for d in Q at target c+(Q[0])?
    coef_real = newton_coef(cs_real, inv, q)
    tgt = cptab[Q[0]] % q
    inv_roots = [d for d in range(n) if newton_eval(coef_real, ds, d, q) == tgt]
    inv_inQ = [d for d in inv_roots if d in set(Q)]

    # low-D decision (prereg §4): pi_obs <= 0.01 AND unique inversion in Q
    low_d = ((sum(1 for h in hist if h <= Dobs) + 1) * 100 <= (NDRAWS + 1)) and (len(inv_inQ) == 1)
    print(f"   q={q}: D_obs={Dobs}  pi={pi_obs:.4f} | null: min={hist[0]} q01={hist[max(0,NDRAWS//100)]} "
          f"med={hist[NDRAWS//2]} max={hist[-1]}  distinct_degs={distinct_degs}", flush=True)
    print(f"     control ii ({note}): D_plant={Dplant} pi={pi_plant:.4f} FIRE={fired_ii}", flush=True)
    print(f"     control iii (calibration): frac(pi<=0.01)={cal_low_cnt/NDRAWS:.4f} (~0.01 wanted); "
          f"null spread = {hist[-1]-hist[0]}", flush=True)
    print(f"     INV at Q[0]: roots in Q = {inv_inQ} (all roots in [0,n): {len(inv_roots)})", flush=True)
    print(f"     >>> LOW-D (channel) = {low_d}   [D_obs at {pi_obs:.3f} of the mu3-null]", flush=True)
    return dict(p=p, q=q, D_obs=Dobs, pi_obs=pi_obs, D_plant=Dplant, fired_ii=fired_ii,
                null_min=hist[0], null_max=hist[-1], null_med=hist[NDRAWS//2],
                cal_low=cal_low_cnt/NDRAWS, inv_inQ=inv_inQ, low_d=low_d)

if __name__ == "__main__":
    for fn in sys.argv[1:]:
        print("=" * 96)
        analyze(fn)
