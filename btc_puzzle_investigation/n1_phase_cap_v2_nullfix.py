#!/usr/bin/env python3
"""N-PERM rebuilt with the CORRECT per-stratum parity (bug fix, see DEVIATIONS D1).

h(lambda d) = h(d) in BOTH strata, but
    p = 3 mod 4 (ODD) : h(-d) = -h(d)   -> orbit sign pattern +-
    p = 1 mod 4 (EVEN): h(-d) = +h(d)   -> orbit sign pattern ++
The v1 run applied the ODD convention to both, so the EVEN null did not carry the
symmetry the readout has by definition.  S is unaffected (computed from h directly).
"""
import json, hashlib
import numpy as np
from sympy.ntheory.residue_ntheory import nthroot_mod
from n1_phase_cap_v2_run import load_holdout, orbit_y, mu6_structure

rows, _ = load_holdout()
out = []
for k, (band, strat, p, n, tr) in enumerate(rows):
    h, _ = orbit_y(p, n)
    lam = [int(z) for z in nthroot_mod(1, 3, n, all_roots=True) if z != 1][0]
    idx, sgn_odd, M = mu6_structure(n, lam)
    sgn = sgn_odd if p % 4 == 3 else np.ones_like(sgn_odd)     # THE FIX
    hs = h[1:] * sgn
    so = np.zeros(M, dtype=np.int8); so[idx] = hs
    ok = bool(np.array_equal(so[idx], hs))                      # C-ORBIT, per stratum
    rng = np.random.default_rng(int(hashlib.sha256(f"nperm2{p}".encode()).hexdigest()[:8], 16))
    hn = np.zeros(n); hn[1:] = so[rng.permutation(M)][idx] * sgn
    V = np.fft.fft(hn)
    Sn = float(np.abs(V)[1:].max() / np.sqrt(p))
    pur = float((np.max(np.abs(V[1:].real)) if p % 4 == 3 else np.max(np.abs(V[1:].imag)))
                / np.max(np.abs(V[1:])))
    pars = float(abs((np.abs(V) ** 2).sum() - n * (n - 1)) / (n * (n - 1)))
    out.append(dict(p=p, strat=strat, S_nperm=Sn, orbit_ok=ok, purity=pur, parseval=pars))
    json.dump(out, open("n1_phase_cap_v2_nullfix.json", "w"))
    if k % 30 == 0: print(f"   [{k+1}/120] p={p} {strat} S_null={Sn:.3f} orb={ok}", flush=True)

for st in ("ODD", "EVEN"):
    d = [x for x in out if x["strat"] == st]
    S = np.array([x["S_nperm"] for x in d])
    n_ = [r[3] for r in rows if r[1] == st]
    pred = np.mean([np.sqrt(2 * np.log((v - 1) / 3)) for v in n_])
    print(f"\n  {st}: C-ORBIT {sum(x['orbit_ok'] for x in d)}/{len(d)}   "
          f"purity<={max(x['purity'] for x in d):.1e}  parseval<={max(x['parseval'] for x in d):.1e}")
    print(f"        N-PERM S: mean {S.mean():.3f}  min {S.min():.3f}  max {S.max():.3f}   "
          f"F7 predicts {pred:.3f}   #(S<=2) = {int((S<=2).sum())}  "
          f"{'HALT' if (S<=2).any() else 'no halt'}")
