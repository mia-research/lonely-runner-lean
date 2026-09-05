#!/usr/bin/env python3
"""Corrected phase probe: empirical GLOBAL-repartition null (one regrouping shared across all
(a0,c) blocks) over all 9 primes. This is the calibrated decision; the analytic per-block null
underestimated variance ~2.85x (see phase_null_diagnostic). Reports per-prime analytic Z (biased)
and empirical global Z (correct), plus Stouffer pooled for both. 6 a-reps (Z_emp is ~areps-invariant)."""
import sys, math, importlib.util
import numpy as np
spec = importlib.util.spec_from_file_location("ph", "btc_puzzle_investigation/mu3_phase_within_triple_v1.py")
sys.argv = ["x"]; ph = importlib.util.module_from_spec(spec); spec.loader.exec_module(ph); mag = ph.mag

def one(p, n_areps=6, B=400, seed=0):
    pp, n, G, X, Y, beta, lam = mag.setup_curve(p, 0, 7)
    reps, tri = mag.build_triples(p, beta); R = len(reps); T = tri.shape[0]
    areps = mag.a_reps(n, lam, n_areps); rng = np.random.default_rng(seed)
    reparts = np.stack([rng.permutation(R).reshape(T, 3) for _ in range(B)])
    d = np.arange(1, n); P_obs = 0.0; E_an = 0.0; V_an = 0.0; P_null = np.zeros(B)
    for a0 in areps:
        W = np.exp(2j*np.pi*a0*d/n)
        for c in range(1, p):
            r = np.real(ph.U_column(W, X, Y, c, p)[reps])
            P_obs += ph.P_obs(r, tri); e, v = ph.null_P_moments(r); E_an += e; V_an += v
            rg = r[reparts]; ps = rg[..., 0]*rg[..., 1] + rg[..., 0]*rg[..., 2] + rg[..., 1]*rg[..., 2]
            P_null += ps.sum(axis=1)
    Za = -(P_obs - E_an)/math.sqrt(V_an)
    Ze = -(P_obs - P_null.mean())/P_null.std()
    return Za, Ze

primes = [2089, 2143, 4159, 8191, 8209, 8293, 16477, 19231, 19249]
Zas, Zes = [], []
for p in primes:
    Za, Ze = one(p)
    Zas.append(Za); Zes.append(Ze)
    print(f"[p={p:5d}] analytic Z={Za:+.3f} (biased)   empirical GLOBAL-null Z={Ze:+.3f} (correct)", flush=True)
print(f"[POOLED] analytic Stouffer = {sum(Zas)/math.sqrt(len(Zas)):+.3f}  (artifact)")
print(f"[POOLED] CORRECTED Stouffer = {sum(Zes)/math.sqrt(len(Zes)):+.3f}  <-- decision statistic")
