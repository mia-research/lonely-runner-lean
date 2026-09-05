#!/usr/bin/env python3
# -*- coding: utf:8 -*-
"""
brick_e_analysis_v1.py — the analysis layer of the powered Brick E rung, per PREREG v2 §§3-5.
Input: brick_e_rung_<p>_data.json (from brick_e_rung_v1.sage). Pure python, exact integers.

  - orbit reps of the QR half under d -> lam*d; kappa_eff from the real data (globality)
  - degree statistic per LARGE prime factor of |A_new| (reps distinct mod q), fit over the FULL
    QR-half table (the polynomial must match the covariantly-propagated values everywhere)
  - null: >=2000 draws, uniform on reps mod M, propagated by kappa_eff (the prereg's law);
    D-histogram per factor; pi = null percentile of D_obs (low-D = pi <= 0.01)
  - control (ii): covariant plant a*d^i0 (i0 with lam^i0 = kappa_eff mod M if it exists, else the
    propagated-from-reps monomial, deviation logged); must FIRE (pi <= 0.01)
  - control (iii): calibration — null draws' own pi values ~ Uniform[0,1] (fraction <= 0.01 ~ 1%)
  - INV: the degree-D fit inverts uniquely for d in Q at the target
"""
import json, random, sys, math
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from brick_e_degree_fitter_v1 import min_degree_fit, invert_fit, factorize

def analyze(fn):
    D = json.load(open(fn))
    p, n, M = D["p"], D["n"], D["M"]
    lam, kappa = D["lam"], D["kappa"]
    cptab = {int(d): int(e) for d, e in D["cplus"].items()}
    Q = sorted(cptab)
    # kappa_eff: the actual propagation ratio on orbits
    ratios = set()
    for d in Q:
        d2 = (lam * d) % n
        if d2 in cptab and math.gcd(cptab[d], M) == 1:
            ratios.add(cptab[d2] * pow(cptab[d], -1, M) % M)
    assert len(ratios) == 1, f"kappa not global on invertible values: {ratios}"
    keff = ratios.pop()
    assert keff in (kappa, kappa * kappa % M) if kappa else True
    # orbits + reps
    seen = set(); reps = []
    for d in Q:
        if d in seen: continue
        reps.append(d)
        x = lam * d % n
        while x != d:
            seen.add(x); x = lam * x % n
        seen.add(d)
    print(f" p={p} n={n} M={M}={factorize(M)} |Q|={len(Q)} reps={len(reps)} kappa_eff={keff} "
          f"(sigma-kappa {kappa})", flush=True)
    # large factors: reps distinct mod q
    facs = [q for q, e in factorize(M).items()]
    large = [q for q in facs if len(set(r % q for r in reps)) == len(reps)]
    print(f" CRT factors {facs} -> large (reps distinct): {large}", flush=True)

    def propagate(repvals):
        """full Q table from rep values mod M, by the covariance law e(lam d) = keff e(d)"""
        kinv = pow(keff, -1, M)
        tab = {}
        for d in Q:
            x = d; j = 0
            while x not in repvals:
                x = lam * x % n; j += 1
                assert j < 3
            # x is j FORWARD steps from d: e(x) = keff^j e(d)  =>  e(d) = keff^{-j} e(x)
            tab[d] = repvals[x] * pow(kinv, j, M) % M
        return tab

    real_reps = {r: cptab[r] for r in reps}
    assert propagate(real_reps) == cptab, "covariance reproduction failed"
    results = {}
    for q in large:
        Dobs, coeffs = min_degree_fit({d: cptab[d] % q for d in Q}, q)
        # null
        random.seed(20260820 + p)
        NDRAWS = 2000
        hist = []
        for _ in range(NDRAWS):
            rv = {r: random.randrange(M) for r in reps}
            tab = propagate(rv)
            dnull, _ = min_degree_fit({d: tab[d] % q for d in Q}, q)
            hist.append(dnull if dnull is not None else 10**9)   # None = beyond-max (strongest)
        hist.sort()
        def pctile(dv):
            # pi = Pr_null(D <= D_obs): LOW D is the signal, so a LOW pi means low-degree
            cnt = sum(1 for h in hist if h <= dv)
            return (cnt + 1) / (NDRAWS + 1)
        pi_obs = pctile(Dobs if Dobs is not None else 10**9)
        # control (ii): search an EXACTLY covariant monomial a*d^i0 on Q; else plain deg-2 plant
        i0 = None; a_plant = None
        for i in range(1, 4 * n):
            if pow(lam, i, M) != keff % M:
                # exact covariance on Q must still be checked (mod-n wraps break monomials)
                pass
            ok = True
            for d in Q:
                if (pow((lam * d) % n, i, M)) != keff * pow(d, i, M) % M:
                    ok = False; break
            if ok:
                i0 = i; a_plant = 1; break
        if i0 is not None:
            plant = {d: pow(d, i0, M) for d in Q}
            note = f"exactly covariant monomial i0={i0} (verified on all Q)"
        else:
            plant = {d: (77 * d * d + 123) % M for d in Q}
            note = "plain degree-2 plant (NO exactly-covariant monomial exists on Q — deviation logged)"
        Dplant, cplant = min_degree_fit({d: plant[d] % q for d in Q}, q)
        pi_plant = pctile(Dplant if Dplant is not None else 10**9)
        fired_ii = pi_plant <= 0.01
        # control (iii): calibration — null draws' own percentiles
        pis = [pctile(h) for h in hist]
        cal_low = sum(1 for x in pis if x <= 0.01) / NDRAWS
        cal_unif = all(0.001 <= sum(1 for h in hist if h < x0) / NDRAWS <= 0.999 for x0 in hist[:100])
        # INV: unique inversion within Q at a target
        inv_ok = None
        if coeffs is not None and Dobs is not None:
            tgt = cptab[Q[0]] % q
            roots = invert_fit(coeffs, tgt, q, n)
            inv_ok = [d for d in roots if d in Q]
        results[q] = dict(D_obs=Dobs, pi_obs=pi_obs, D_plant=Dplant, pi_plant=pi_plant,
                          fired_ii=fired_ii, cal_low=cal_low, cal_unif=cal_unif,
                          inv=inv_ok, note=note,
                          null_q01=hist[int(0.01 * NDRAWS)], null_med=hist[NDRAWS // 2],
                          null_max=hist[-1])
        r = results[q]
        print(f"   q={q}: D_obs={r['D_obs']}  pi={r['pi_obs']:.4f} | null q01={r['null_q01']} "
              f"med={r['null_med']} max={r['null_max']}", flush=True)
        print(f"     control ii (plant, {r['note']}): D={r['D_plant']} pi={r['pi_plant']:.4f} "
              f"FIRE={r['fired_ii']}", flush=True)
        print(f"     control iii (calibration): frac(pi<=0.01)={r['cal_low']:.4f} (~0.01 wanted); "
              f"uniformity={r['cal_unif']}", flush=True)
        print(f"     INV at Q[0]: inversions within Q = {r['inv']}", flush=True)
    return results

if __name__ == "__main__":
    for fn in sys.argv[1:]:
        print("=" * 100)
        analyze(fn)
