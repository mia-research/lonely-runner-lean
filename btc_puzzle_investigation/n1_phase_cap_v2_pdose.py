#!/usr/bin/env python3
"""P-DOSE (spec 3.4c) — the fragility calibration, on the 20 FROZEN plant primes.

Balanced orbit-sign swaps interpolate eps=0 (the real readout, S<=2) to eps=0.5
(= N-PERM exactly, S~4.2).  BOTH ENDPOINTS KNOWN IN ADVANCE.  eps* = the smallest
swept eps at which S crosses 2.

PRE-COMMITTED (spec 3.4c): eps* <= 0.10 => the cap is FRAGILE, so chi2(y) sitting
under it is informative.  eps* >= 0.25 => the cap is NEAR-VACUOUS and the question
as posed is uninteresting.  Derived prediction eps*_pred = (1-rho*)/2 with
rho*^2 = 1 - 3/(T^2-1), T = 2*sqrt(p)/rms -- computed per prime before reading S.
"""
import json
import numpy as np
from sympy.ntheory.residue_ntheory import nthroot_mod
from n1_phase_cap_v2_run import load_holdout, orbit_y, mu6_structure

EPS = [0.02, 0.05, 0.10, 0.15, 0.20, 0.25, 0.35, 0.50]
rows, _ = load_holdout()
seen = set(); plant = []
for b, s, p, n, t in rows:
    if (b, s) not in seen:
        seen.add((b, s)); plant.append((b, s, p, n))
print(f"  P-DOSE on the {len(plant)} frozen plant primes\n")
print(f"{'p':>8} {'strat':>5} " + " ".join(f"e={e:<5}" for e in EPS) + "  eps*  pred")
res = []
for b, st, p, n in plant:
    h, _ = orbit_y(p, n)
    lam = [int(z) for z in nthroot_mod(1, 3, n, all_roots=True) if z != 1][0]
    idx, sgn_odd, M = mu6_structure(n, lam)
    sgn = sgn_odd if p % 4 == 3 else np.ones_like(sgn_odd)
    so = np.zeros(M, dtype=np.int8); so[idx] = h[1:] * sgn
    rng = np.random.default_rng(int(p))
    order = rng.permutation(M)
    S = []
    for e in EPS:
        k = int(round(e * M)) * 2                     # balanced: swap k orbit signs in pairs
        k = min(k, M)
        so2 = so.copy()
        if k: so2[order[:k]] = so[order[:k][::-1]]    # pairwise swap => sign multiset exact
        hn = np.zeros(n); hn[1:] = so2[idx] * sgn
        S.append(float(np.abs(np.fft.fft(hn))[1:].max() / np.sqrt(p)))
    star = next((e for e, s_ in zip(EPS, S) if s_ > 2.0), None)
    rms = np.sqrt(n - 1); T = 2 * np.sqrt(p) / rms
    rho2 = max(0.0, 1 - 3 / max(T * T - 1, 1e-9)); pred = (1 - np.sqrt(rho2)) / 2
    res.append(dict(p=p, strat=st, S=S, star=star, pred=float(pred)))
    print(f"{p:>8} {st:>5} " + " ".join(f"{s_:<7.3f}" for s_ in S) +
          f"  {str(star):>5} {pred:.3f}")
json.dump(res, open("n1_phase_cap_v2_pdose.json", "w"))
st = [r["star"] for r in res if r["star"] is not None]
print(f"\n  eps* found at {len(st)}/{len(res)} plant primes; median eps* = "
      f"{np.median(st) if st else float('nan')}")
if st:
    m = float(np.median(st))
    verdict = ("FRAGILE => the cap is informative" if m <= 0.10 else
               "NEAR-VACUOUS => question uninteresting as posed" if m >= 0.25 else
               "INTERMEDIATE => neither pre-committed branch")
    print(f"  PRE-COMMITTED READ: median eps* = {m} -> {verdict}")
