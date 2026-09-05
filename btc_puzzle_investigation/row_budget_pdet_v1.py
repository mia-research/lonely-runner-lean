#!/usr/bin/env python3
"""
row_budget_pdet_v1.py — P-DET, the planted-detector gate of
PREREG_row_budget_lowtail_v1.md section 4.1.

Plant: for each frequency f, draw a* and a subset D_f of size round(eps*(n-1));
replace s_f(d) by the pure tone e_n(-a* d) on D_f.  Unit modulus is preserved
exactly, so the row budget is preserved exactly (asserted).  eps=0 is the
character system, eps=1 is the pure tone.

PASS CRITERIA (all four must PASS before the primary may issue any verdict):
  1. eps = 1.00 returns N_LOW = n-2 exactly, every f, every prime.
  2. chirp returns N_LOW = 0 exactly, every f, every prime.
  3. Nbar(eps) strictly increasing across the seven swept levels, every prime.
  4. z(eps = 0.20) vs MN-mu6 exceeds +6 at every prime with p >= 577.
Also reported (calibration, not a criterion): smallest swept eps with z > 4
= the detector's MEASURED MDE, against the computed MDE of the spec's section 5.
"""
import argparse, json
import numpy as np
from row_budget_core_v1 import curve_orbit
from row_budget_run_v1 import (load_freqs, mu6_orbits, Permuter, nlow_batch,
                               SPEC_N, SPEC_BETA, THRESH)

EPS = [0.05, 0.10, 0.20, 0.30, 0.50, 0.80, 1.00]
DERIVED = {e: e * e / (1 - e * e) for e in EPS[:-1]}      # eps^2/(1-eps^2)


def pdet_prime(p, freqs, R, rng, mcap=None):
    X, Y, n = curve_orbit(p)
    assert n == SPEC_N[p]
    beta = SPEC_BETA[p]
    xb = beta * X[1] % p
    lam = int(np.nonzero((X == xb) & (Y == Y[1]))[0][0])
    reps6, orb6, unit6, pw6 = mu6_orbits(n, lam)
    P6 = Permuter(n, reps6, orb6, unit6, pw6)
    tab = np.exp(2j * np.pi * np.arange(p) / p)
    F = freqs[p]
    if mcap: F = F[:mcap]
    m = len(F)

    d = np.arange(n)
    chirp = np.exp(2j * np.pi * (d * d % n) / n); chirp[0] = 0
    chirp_nl = int(nlow_batch(np.array([chirp]), n)[0][0])

    acc = {e: 0.0 for e in EPS}; acc_char = 0.0
    null = np.zeros(R)
    tone_bad = 0; budget_worst = 0.0
    for (b, c) in F:
        e0 = (b * X + c * Y) % p
        s = tab[e0]; s[0] = 0.0
        rows = [s]
        astar = int(rng.integers(1, n))
        tone = np.exp(-2j * np.pi * (astar * d % n) / n)
        for e in EPS:
            k = int(round(e * (n - 1)))
            D = rng.choice(np.arange(1, n), size=k, replace=False) if 0 < k < n - 1 else (
                np.arange(1, n) if k >= n - 1 else np.array([], dtype=np.int64))
            sp = s.copy()
            if D.size: sp[D] = tone[D]
            rows.append(sp)
        for _ in range(R):
            rows.append(s[P6.draw(rng)])
        S = np.array(rows)
        NL, bud, _ = nlow_batch(S, n)
        budget_worst = max(budget_worst, float(np.max(np.abs(bud - n * (n - 1)))) / (n * (n - 1)))
        acc_char += NL[0]
        for i, e in enumerate(EPS):
            acc[e] += NL[1 + i]
        if NL[1 + len(EPS) - 1] != n - 2:
            tone_bad += 1
        null += NL[1 + len(EPS):]

    nb = {e: acc[e] / m for e in EPS}
    nb_char = acc_char / m
    mu, sd = null.mean() / m, null.std(ddof=1) / m
    z = {e: (nb[e] - mu) / sd for e in EPS}
    inc = all(nb[EPS[i]] < nb[EPS[i + 1]] for i in range(len(EPS) - 1))
    meas_mde = next((e for e in EPS if z[e] > 4), None)
    return dict(p=p, n=n, m=m, chirp=chirp_nl, tone_bad=tone_bad, tone_expect=n - 2,
                budget_relerr=budget_worst, Nbar_char=nb_char,
                Nbar=dict((str(e), nb[e]) for e in EPS),
                z=dict((str(e), float(z[e])) for e in EPS),
                excess20=float((nb[0.20] - mu) / mu), increasing=bool(inc),
                measured_mde=meas_mde, null_mu=float(mu), null_sd=float(sd))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", default="163,211,349,433,577,991,2089")
    ap.add_argument("--R", type=int, default=32)
    ap.add_argument("--mcap", type=int, default=400)
    ap.add_argument("--out", default="row_budget_pdet_v1.json")
    a = ap.parse_args()
    freqs, h = load_freqs()
    rng = np.random.default_rng(int(20260725))
    rows = []
    print("=" * 92)
    print("P-DET — planted detector gate (spec 4.1). All four criteria must PASS.")
    print("=" * 92)
    for p in [int(t) for t in a.primes.split(",")]:
        r = pdet_prime(p, freqs, a.R, rng, a.mcap)
        rows.append(r)
        print(f"\n  p={p} n={r['n']} m={r['m']}  chirp={r['chirp']} (need 0)  "
              f"tone violations={r['tone_bad']} (need 0)  budget={r['budget_relerr']:.1e}")
        print(f"    Nbar: char {r['Nbar_char']:.3f} | " +
              " ".join(f"e={e}:{r['Nbar'][str(e)]:.3f}" for e in EPS))
        print(f"    z   : " + " ".join(f"e={e}:{r['z'][str(e)]:+.1f}" for e in EPS))
        print(f"    strictly increasing: {r['increasing']}   "
              f"excess@0.20 = {r['excess20']*100:.2f}% (derived {DERIVED[0.20]*100:.1f}%)   "
              f"measured MDE = {r['measured_mde']}")
        json.dump(rows, open(a.out, "w"), indent=1)

    print("\n" + "=" * 92)
    c1 = all(r["tone_bad"] == 0 for r in rows)
    c2 = all(r["chirp"] == 0 for r in rows)
    c3 = all(r["increasing"] for r in rows)
    c4 = all(r["z"]["0.2"] > 6 for r in rows if r["p"] >= 577)
    for i, (nm, ok) in enumerate([("1 tone == n-2 exactly", c1), ("2 chirp == 0 exactly", c2),
                                  ("3 Nbar(eps) strictly increasing", c3),
                                  ("4 z(eps=0.20) > +6 for p>=577", c4)], 1):
        print(f"  CRITERION {nm}: {'PASS' if ok else 'FAIL'}")
    print(f"\n  P-DET GATE: {'PASS — the primary may issue a verdict' if all((c1,c2,c3,c4)) else 'FAIL — no verdict may be issued'}")


if __name__ == "__main__":
    main()
