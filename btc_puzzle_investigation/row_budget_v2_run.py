#!/usr/bin/env python3
"""
row_budget_v2_run.py — executes PREREG_row_budget_lowtail_v2.md, Arm A + gates.

AMENDED PLANT (spec 4.1), four named changes from v1:
  (C-a) carrier = an MN-mu6 draw on a stream DISJOINT from the R verdict
        replicates -- not the character.  A positive control certifies the power
        of the DECISION RULE (null spread x statistic response); both are
        properties of the null and the statistic.
  (C-b) plant target = the CONSTANT t(d) == 1  (a* = 0), so the spike lands on
        the a=0 row that N_LOW excludes by definition (F4).  The F12
        cancellation disappears and the response model becomes exact and
        provably monotone:
            Delta_pred(eps) = (1 - exp(-th/(1-eps^2)))/(1 - exp(-th)) - 1
  (C-c) NESTED subsets D_f(eps1) subset D_f(eps2), one chain per frequency.
  (C-d) PAIRED baseline: the eps=0 cell is the SAME carrier, unplanted.

FIVE PASS CRITERIA (all must PASS before any Arm A verdict):
  1  eps=1.00 -> N_LOW = n-1 exactly            (changed from v1's n-2, F14)
  2  chirp    -> N_LOW = 0     exactly
  3  |Delta_meas - Delta_pred| <= max(3 SE, 0.5|Delta_pred|) on the ADMISSIBLE
     sub-grid, and Delta_meas strictly increasing across it
  4  z(eps=0.20) vs MN-mu6 > +6 for every p >= 577
  5  P-SIZE (negative control): the UNPLANTED carrier must not fire

Plus C-SELFZ (null self-calibration) and C-DISP (dispersion gate).

Arm A is capped at [EMPIRICAL - SEEN-DATA, CONTROL-REPAIRED] by spec section 0.
"""
import argparse, json
import numpy as np
from row_budget_core_v1 import curve_orbit
from row_budget_run_v1 import (load_freqs, mu6_orbits, neg_orbits, Permuter,
                               free_perm, SPEC_N, SPEC_BETA, THRESH)

EPS = [0.05, 0.10, 0.15, 0.20, 0.30, 0.50, 0.80, 1.00]
FIRST_ADM = {163: 0.30, 211: 0.20, 349: 0.15, 433: 0.15, 577: 0.10,
             991: 0.10, 2089: 0.10, 4159: 0.10, 9319: 0.10, 19231: 0.10}


def delta_pred(e, th=THRESH):
    """Exp(1) carrier (generic stratum). Exact, n-free, strictly increasing."""
    if e >= 1.0:
        return None
    return (1 - np.exp(-th / (1 - e * e))) / (1 - np.exp(-th)) - 1


def setup(p):
    X, Y, n = curve_orbit(p)
    assert n == SPEC_N[p], f"n mismatch at p={p}"
    beta = SPEC_BETA[p]
    assert pow(beta, 3, p) == 1 and beta != 1
    lam = int(np.nonzero((X == beta * X[1] % p) & (Y == Y[1]))[0][0])
    ceq = int(np.max((X[(lam * np.arange(n)) % n] - beta * X) % p))
    assert ceq == 0, f"C-EQ-int failed p={p}"
    return X, Y, n, Permuter(n, *mu6_orbits(n, lam)), Permuter(n, *neg_orbits(n)), ceq


def run_prime(p, freqs, R, rngA, rngB, verbose=True):
    X, Y, n, P6, P2, ceq = setup(p)
    tab = np.exp(2j * np.pi * np.arange(p) / p)
    F = freqs[p]; m = len(F)
    d = np.arange(n)
    chirp = np.exp(2j * np.pi * (d * d % n) / n); chirp[0] = 0

    NLc = np.zeros(m)
    NLa = np.zeros((R, m))            # stream A: verdict replicates (MN-mu6)
    NLb = np.zeros((R, m))            # stream B: independent carriers (MN-mu6)
    NLneg = np.zeros((R, m)); NLfree = np.zeros((R, m))
    NLp = np.zeros((len(EPS), m))     # plant on carrier B[0]
    NL0 = np.zeros(m)                 # paired eps=0 cell = carrier B[0] unplanted
    chirp_bad = 0; tone_bad = 0; budget_worst = 0.0

    for i, (b, c) in enumerate(F):
        e0 = (b * X + c * Y) % p
        s = tab[e0]; s[0] = 0.0
        permsA = [P6.draw(rngA) for _ in range(R)]
        permsB = [P6.draw(rngB) for _ in range(R)]
        rows = [s]
        rows += [s[q] for q in permsA]
        rows += [s[q] for q in permsB]
        rows += [s[P2.draw(rngA)] for _ in range(R)]
        rows += [s[free_perm(n, rngA)] for _ in range(R)]

        carrier = s[permsB[0]]
        rows.append(carrier)                              # eps = 0, paired baseline
        order = rngB.permutation(np.arange(1, n))         # ONE nested chain per f
        for e in EPS:
            k = int(round(e * (n - 1)))
            sp = carrier.copy()
            if k > 0:
                sp[order[:k]] = 1.0 + 0.0j                # constant target t == 1
            rows.append(sp)
        rows.append(chirp)

        U2 = np.abs(np.fft.fft(np.array(rows), axis=1)) ** 2
        budget_worst = max(budget_worst,
                           float(np.max(np.abs(U2.sum(1) - n * (n - 1)))) / (n * (n - 1)))
        nl = (U2[:, 1:] / (n - 1) < THRESH).sum(1)
        o = 0
        NLc[i] = nl[o]; o += 1
        NLa[:, i] = nl[o:o + R]; o += R
        NLb[:, i] = nl[o:o + R]; o += R
        NLneg[:, i] = nl[o:o + R]; o += R
        NLfree[:, i] = nl[o:o + R]; o += R
        NL0[i] = nl[o]; o += 1
        NLp[:, i] = nl[o:o + len(EPS)]; o += len(EPS)
        if nl[o] != 0: chirp_bad += 1
        if NLp[-1, i] != n - 1: tone_bad += 1

    # ---- Arm A primary: paired per-frequency error model
    nullmean_f = NLa.mean(0)
    delta_f = NLc - nullmean_f
    Nbar_c = NLc.mean(); Nbar_null = NLa.mean()
    Dbar = delta_f.mean(); SE = delta_f.std(ddof=1) / np.sqrt(m)
    repl = NLa.mean(1)
    z = (Nbar_c - repl.mean()) / repl.std(ddof=1)
    rank_p = (1 + int((repl >= Nbar_c).sum())) / (R + 1.0)

    # ---- C-DISP
    D_char = NLc.var(ddof=1) / NLc.mean()
    D_null = float(np.mean([NLa[r].var(ddof=1) / NLa[r].mean() for r in range(R)]))
    disp = D_char / D_null
    SE_infl = SE * np.sqrt(disp) if disp > 1.5 else SE

    # ---- C-SELFZ
    h1, h2 = repl[:R // 2], repl[R // 2:]
    z_split = (h1.mean() - h2.mean()) / h2.std(ddof=1)
    loo = np.array([(repl[k] - np.delete(repl, k).mean()) / np.delete(repl, k).std(ddof=1)
                    for k in range(R)])

    # ---- P-SIZE: each independent carrier vs the stream-A distribution
    zb = (NLb.mean(1) - repl.mean()) / repl.std(ddof=1)
    psize_frac = float((np.abs(zb) > 2).mean()); psize_max = float(np.abs(zb).max())

    # ---- P-DET criterion 3: paired Delta_meas vs Delta_pred
    base = NL0.mean()
    dmeas = {}; dse = {}
    boot = rngB.integers(0, m, size=(200, m))
    for j, e in enumerate(EPS):
        diff = NLp[j] - NL0
        dmeas[e] = diff.mean() / base
        dse[e] = float(np.std([diff[bi].mean() / NL0[bi].mean() for bi in boot], ddof=1))
    z20 = (NLp[EPS.index(0.20)].mean() - repl.mean()) / repl.std(ddof=1)

    adm = [e for e in EPS if e >= FIRST_ADM[p] and e < 1.0]
    c3_ok = True; c3_detail = []
    for e in adm:
        dp = delta_pred(e)
        tol = max(3 * dse[e], 0.5 * abs(dp))
        ok = abs(dmeas[e] - dp) <= tol
        c3_ok &= ok
        c3_detail.append((e, dmeas[e], dp, tol, ok))
    mono = all(dmeas[adm[i]] < dmeas[adm[i + 1]] for i in range(len(adm) - 1))
    c3_ok &= mono

    out = dict(p=p, n=n, m=m, ceq=ceq, budget=budget_worst,
               Nbar_char=float(Nbar_c), Nbar_null=float(Nbar_null),
               Dbar=float(Dbar), SE=float(SE), SE_infl=float(SE_infl),
               excess=float(Dbar / Nbar_null), rel_SE=float(SE_infl / Nbar_null),
               z=float(z), rank_p=rank_p,
               Nbar_neg=float(NLneg.mean()), Nbar_free=float(NLfree.mean()),
               ref_ray=float((n - 1) * (1 - np.exp(-THRESH))),
               D_char=float(D_char), D_null=float(D_null), disp=float(disp),
               z_split=float(z_split), loo_sd=float(loo.std(ddof=1)),
               psize_frac=psize_frac, psize_max=psize_max,
               psize_z=[float(v) for v in zb],
               psize_mean=float(zb.mean()), psize_sd=float(zb.std(ddof=1)),
               chirp_bad=chirp_bad, tone_bad=tone_bad,
               z20=float(z20), adm=adm, mono=bool(mono), c3_ok=bool(c3_ok),
               dmeas={str(e): float(dmeas[e]) for e in EPS},
               dse={str(e): float(dse[e]) for e in EPS})
    if verbose:
        print(f"\n  p={p} n={n} m={m}  C-EQ-int={ceq}  C-BUDGET={budget_worst:.1e}")
        print(f"    excess {out['excess']*100:+.3f}% +- {out['rel_SE']*100:.3f}%  "
              f"z={z:+.2f}  rank-p={rank_p:.4f}")
        print(f"    C-DISP D_char/D_null = {disp:.3f} {'(SE inflated)' if disp>1.5 else ''}"
              f"   C-SELFZ z_split={z_split:+.2f} loo_sd={loo.std(ddof=1):.3f}")
        print(f"    P-SIZE: max|z| over 64 unplanted carriers = {psize_max:.2f}, "
              f"frac|z|>2 = {psize_frac:.3f}")
        print(f"    chirp violations={chirp_bad}  tone(eps=1 -> n-1) violations={tone_bad}")
        print(f"    admissible sub-grid {adm}   monotone={mono}")
        for e, dm, dp, tol, ok in c3_detail:
            print(f"      eps={e:<5} Delta_meas {dm*100:+8.3f}%  pred {dp*100:+8.3f}%  "
                  f"tol {tol*100:6.3f}%  {'PASS' if ok else 'FAIL'}")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", default="163,211,349,433,577,991,2089,4159,9319,19231")
    ap.add_argument("--R", type=int, default=64)
    ap.add_argument("--out", default="row_budget_v2_rows.json")
    a = ap.parse_args()
    freqs, h = load_freqs()
    print(f"  frozen frequency list sha256 {h[:24]}...  OK")
    rngA = np.random.default_rng(int(20260801))      # verdict replicate stream
    rngB = np.random.default_rng(int(20260802))      # carrier / plant stream (disjoint)
    rows = []
    for p in [int(t) for t in a.primes.split(",")]:
        rows.append(run_prime(p, freqs, a.R, rngA, rngB))
        json.dump(rows, open(a.out, "w"), indent=1)

    print("\n" + "=" * 94)
    c1 = all(r["tone_bad"] == 0 for r in rows)
    c2 = all(r["chirp_bad"] == 0 for r in rows)
    c3 = all(r["c3_ok"] for r in rows)
    c4 = all(r["z20"] > 6 for r in rows if r["p"] >= 577)
    c5 = all(r["psize_max"] <= 3 and r["psize_frac"] <= 0.10 for r in rows)
    selfz = all(abs(r["z_split"]) <= 3 and 0.7 <= r["loo_sd"] <= 1.4 for r in rows)
    for nm, ok in [("1 eps=1 -> N_LOW = n-1 exactly", c1),
                   ("2 chirp -> N_LOW = 0 exactly", c2),
                   ("3 Delta_meas ~ Delta_pred on admissible sub-grid", c3),
                   ("4 z(eps=0.20) > +6 for p>=577", c4),
                   ("5 P-SIZE negative control", c5)]:
        print(f"  CRITERION {nm}: {'PASS' if ok else 'FAIL'}")
    print(f"  C-SELFZ: {'PASS' if selfz else 'FAIL'}")
    gate = all((c1, c2, c3, c4, c5, selfz))
    print(f"\n  P-DET-A GATE: {'PASS — Arm A may issue a verdict' if gate else 'FAIL — no verdict'}")
    if gate:
        zs = np.array([r["z"] for r in rows])
        print(f"\n  ARM A  pooled Stouffer Z = {zs.sum()/np.sqrt(len(zs)):+.2f}   "
              f"sign {int((zs>0).sum())}/{len(zs)} positive")
        print("  [EMPIRICAL — SEEN-DATA, CONTROL-REPAIRED] per spec section 0.")


if __name__ == "__main__":
    main()
