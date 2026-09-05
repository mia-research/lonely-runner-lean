#!/usr/bin/env python3
"""
row_budget_v3_run.py -- executes PREREG_row_budget_lowtail_v3.md (frozen 2026-07-25).

Differences from row_budget_v2_run.py, ALL of them pre-registered in v3:
  * criterion 3 tolerance band 3*SE -> 4*SE            (v3 section 4, FFR 0.10-0.15 -> <0.01)
  * criterion 3 monotonicity restricted to the admissible sub-grid pairs whose
    Delta_pred separation exceeds 3*relsd               (v3 section 4, FFR 0.0137)
  * criterion 5 P-SIZE -> P-SIZE' with FOUR clauses     (v3 section 4, FFR 0.8228 -> 0.0783)
  * per-prime spread failure DEFLATES z_p instead of halting  (v3 O-A13)
  * Arm A3 slope band WITHDRAWN -> A3' inverse-variance-weighted constant test (v3 section 3.3),
    which needs the per-prime LAYER SE -- the quantity v2 computed but never stored.

Seeds are the frozen v2 streams so that the ladder is the same object; the only new
random draws are none.  Exactness per v3 section 1 / v2 section 8.
"""
import argparse, json, math
import numpy as np
from row_budget_v2_run import setup, delta_pred, EPS, FIRST_ADM
from row_budget_run_v1 import load_freqs, free_perm, THRESH

# ---- frozen v3 gate constants (computed in row_budget_v3_calib_v*.py, NOT tuned here)
B_MEAN_POOLED = 0.1186      # 3/sqrt(640)
B_SD_POOLED   = 0.0839      # 3/sqrt(1280)
B_MAX_POOLED  = 3.9440      # (2*Phi(q)-1)^640 = 0.95
B_SD_PERPRIME = 0.2673      # 3/sqrt(2*63)
A3_C_PRED     = -0.4950     # F11


def run_prime(p, freqs, R, rngA, rngB, verbose=True):
    X, Y, n, P6, P2, ceq = setup(p)
    tab = np.exp(2j * np.pi * np.arange(p) / p)
    F = freqs[p]; m = len(F)
    d = np.arange(n)
    chirp = np.exp(2j * np.pi * (d * d % n) / n); chirp[0] = 0

    NLc = np.zeros(m); NLa = np.zeros((R, m)); NLb = np.zeros((R, m))
    NLneg = np.zeros((R, m)); NLfree = np.zeros((R, m))
    NLp = np.zeros((len(EPS), m)); NL0 = np.zeros(m)
    chirp_bad = tone_bad = 0; budget_worst = 0.0

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
        rows.append(carrier)
        order = rngB.permutation(np.arange(1, n))
        for e in EPS:
            k = int(round(e * (n - 1)))
            sp = carrier.copy()
            if k > 0:
                sp[order[:k]] = 1.0 + 0.0j
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

    nullmean_f = NLa.mean(0)
    delta_f = NLc - nullmean_f
    Nbar_c = NLc.mean(); Nbar_null = NLa.mean()
    Dbar = delta_f.mean(); SE = delta_f.std(ddof=1) / np.sqrt(m)
    repl = NLa.mean(1)
    z = (Nbar_c - repl.mean()) / repl.std(ddof=1)
    rank_p = (1 + int((repl >= Nbar_c).sum())) / (R + 1.0)

    D_char = NLc.var(ddof=1) / NLc.mean()
    D_null = float(np.mean([NLa[r].var(ddof=1) / NLa[r].mean() for r in range(R)]))
    disp = D_char / D_null
    SE_infl = SE * np.sqrt(disp) if disp > 1.5 else SE

    h1, h2 = repl[:R // 2], repl[R // 2:]
    z_split = (h1.mean() - h2.mean()) / h2.std(ddof=1)
    loo = np.array([(repl[k] - np.delete(repl, k).mean()) / np.delete(repl, k).std(ddof=1)
                    for k in range(R)])

    zb = (NLb.mean(1) - repl.mean()) / repl.std(ddof=1)

    # ---- NEW for v3: the A3' layer, per frequency, with its own SE
    ref_ray = (n - 1) * (1 - np.exp(-THRESH))
    layer_f = NLfree.mean(0) - ref_ray                       # per frequency
    layer_mean = float(layer_f.mean())
    layer_se = float(layer_f.std(ddof=1) / np.sqrt(m))
    layer_pct = 100.0 * layer_mean / ref_ray
    layer_se_pct = 100.0 * layer_se / ref_ray

    base = NL0.mean()
    dmeas = {}; dse = {}
    boot = rngB.integers(0, m, size=(200, m))
    for j, e in enumerate(EPS):
        diff = NLp[j] - NL0
        dmeas[e] = diff.mean() / base
        dse[e] = float(np.std([diff[bi].mean() / NL0[bi].mean() for bi in boot], ddof=1))
    z20 = (NLp[EPS.index(0.20)].mean() - repl.mean()) / repl.std(ddof=1)

    adm = [e for e in EPS if e >= FIRST_ADM[p] and e < 1.0]
    relsd = float(SE_infl / Nbar_null)
    c3_ok = True; c3_detail = []
    for e in adm:
        dp = delta_pred(e)
        tol = max(4 * dse[e], 0.5 * abs(dp))          # v3: 3 -> 4 SE
        ok = abs(dmeas[e] - dp) <= tol
        c3_ok &= ok
        c3_detail.append((e, dmeas[e], dp, tol, ok))
    # v3: monotonicity only across pairs separated by more than 3*relsd in Delta_pred
    mono = True; mono_pairs = 0
    for i in range(len(adm) - 1):
        if abs(delta_pred(adm[i + 1]) - delta_pred(adm[i])) > 3 * relsd:
            mono_pairs += 1
            if not (dmeas[adm[i]] < dmeas[adm[i + 1]]):
                mono = False
    c3_ok &= mono

    out = dict(p=p, n=n, m=m, ceq=ceq, budget=budget_worst,
               Nbar_char=float(Nbar_c), Nbar_null=float(Nbar_null),
               Dbar=float(Dbar), SE=float(SE), SE_infl=float(SE_infl),
               excess=float(Dbar / Nbar_null), rel_SE=relsd,
               z=float(z), rank_p=rank_p,
               Nbar_neg=float(NLneg.mean()), Nbar_free=float(NLfree.mean()),
               ref_ray=float(ref_ray),
               layer_pct=layer_pct, layer_se_pct=layer_se_pct,
               D_char=float(D_char), D_null=float(D_null), disp=float(disp),
               z_split=float(z_split), loo_sd=float(loo.std(ddof=1)),
               psize_z=[float(v) for v in zb],
               psize_mean=float(zb.mean()), psize_sd=float(zb.std(ddof=1)),
               psize_max=float(np.abs(zb).max()),
               psize_frac=float((np.abs(zb) > 2).mean()),
               chirp_bad=chirp_bad, tone_bad=tone_bad,
               z20=float(z20), adm=adm, mono=bool(mono), mono_pairs=mono_pairs,
               c3_ok=bool(c3_ok),
               dmeas={str(e): float(dmeas[e]) for e in EPS},
               dse={str(e): float(dse[e]) for e in EPS})
    if verbose:
        print(f"\n  p={p} n={n} m={m}  C-EQ-int={ceq}  C-BUDGET={budget_worst:.1e}")
        print(f"    excess {out['excess']*100:+.3f}% +- {relsd*100:.3f}%  z={z:+.2f}  "
              f"rank-p={rank_p:.4f}")
        print(f"    layer(MN-free - REF-RAY) = {layer_pct:+.4f}% +- {layer_se_pct:.4f}%   "
              f"C_p = (n-1)*layer = {(n-1)*layer_pct:+.3f}")
        print(f"    C-DISP {disp:.3f}   C-SELFZ z_split={z_split:+.2f} loo_sd={loo.std(ddof=1):.3f}")
        print(f"    P-SIZE' carriers: mean={zb.mean():+.4f} sd={zb.std(ddof=1):.4f} "
              f"max|z|={np.abs(zb).max():.3f} frac|z|>2={float((np.abs(zb)>2).mean()):.4f}")
        print(f"    crit3 sub-grid {adm} gated pairs={mono_pairs} monotone={mono} c3={c3_ok}")
        for e, dm, dp, tol, ok in c3_detail:
            print(f"      eps={e:<5} meas {dm*100:+8.3f}%  pred {dp*100:+8.3f}%  "
                  f"tol(4SE) {tol*100:6.3f}%  {'PASS' if ok else 'FAIL'}")
    return out


def adjudicate(rows):
    print("\n" + "=" * 94)
    print("PREREG_row_budget_lowtail_v3.md -- ADJUDICATION")
    print("=" * 94)
    R = len(rows[0]["psize_z"])
    c1 = all(r["tone_bad"] == 0 for r in rows)
    c2 = all(r["chirp_bad"] == 0 for r in rows)
    c3 = all(r["c3_ok"] for r in rows)
    c4 = all(r["z20"] > 6 for r in rows if r["p"] >= 577)

    allz = [v for r in rows for v in r["psize_z"]]
    pm = float(np.mean(allz)); psd = float(np.std(allz, ddof=1))
    pmx = float(np.max(np.abs(allz)))
    bad_sd = [r["p"] for r in rows if abs(r["psize_sd"] - 1) > B_SD_PERPRIME]
    ci = abs(pm) <= B_MEAN_POOLED
    cii = abs(psd - 1) <= B_SD_POOLED
    ciii = pmx <= B_MAX_POOLED
    civ = len(bad_sd) == 0
    print(f"\nP-SIZE' (frozen bounds, computed pre-run in row_budget_v3_calib_v3.py):")
    print(f"  (i)   pooled |mean|   = {abs(pm):.4f}  <= {B_MEAN_POOLED}  {'PASS' if ci else 'FAIL'}")
    print(f"  (ii)  pooled |sd-1|   = {abs(psd-1):.4f}  <= {B_SD_POOLED}  {'PASS' if cii else 'FAIL'}")
    print(f"  (iii) pooled max|z|   = {pmx:.4f}  <= {B_MAX_POOLED}  {'PASS' if ciii else 'FAIL'}")
    print(f"  (iv)  per-prime |sd-1|<= {B_SD_PERPRIME}: "
          f"{'PASS' if civ else 'FAIL at ' + str(bad_sd)}")

    selfz = all(abs(r["z_split"]) <= 3 and 0.7 <= r["loo_sd"] <= 1.4 for r in rows)
    for nm, ok in [("1 eps=1 -> N_LOW = n-1 exactly", c1),
                   ("2 chirp -> N_LOW = 0 exactly", c2),
                   ("3 Delta_meas ~ Delta_pred, 4 SE band + gated monotonicity", c3),
                   ("4 z(eps=0.20) > +6 for p>=577", c4)]:
        print(f"  CRITERION {nm}: {'PASS' if ok else 'FAIL'}")
    print(f"  C-SELFZ: {'PASS' if selfz else 'FAIL'}")

    # v3 O-A13: clause (iv) deflates, does not halt.  Clauses (i)-(iii) halt.
    halt = not (ci and cii and ciii)
    gate = all((c1, c2, c3, c4, selfz)) and not halt
    print(f"\n  HALT (P-SIZE' i-iii): {halt}    per-prime deflation applies at: {bad_sd}")

    zs = []
    print(f"\n  {'p':>7} {'z_raw':>9} {'sd_p':>8} {'z_used':>9}")
    for r in rows:
        zr = r["z"]
        zu = zr / r["psize_sd"] if abs(r["psize_sd"] - 1) > B_SD_PERPRIME else zr
        zs.append(zu)
        print(f"  {r['p']:>7} {zr:>9.2f} {r['psize_sd']:>8.4f} {zu:>9.2f}"
              + ("   <- deflated (O-A13)" if zu != zr else ""))
    Zpool = float(np.sum(zs) / math.sqrt(len(zs)))
    print(f"\n  ARM A pooled Stouffer Z = {Zpool:+.2f}   "
          f"sign {sum(1 for v in zs if v > 0)}/{len(zs)} positive")

    # ---- A3' : inverse-variance-weighted constant
    print(f"\n  ARM A3' -- F11 constant C = (n-1)*layer, predicted {A3_C_PRED}")
    print(f"  {'p':>7} {'layer %':>10} {'SE %':>9} {'C_p':>10} {'weight %':>9}  seen?")
    SEEN = {163, 433, 991, 2089, 4159, 9319, 19231}
    def a3(sub):
        num = den = 0.0
        for r in sub:
            # F11 states layer as a FRACTION of REF-RAY: C = (n-1)*layer_fraction = -0.4950
            Cp = (r["n"] - 1) * r["layer_pct"] / 100.0
            sig = (r["n"] - 1) * r["layer_se_pct"] / 100.0
            if sig <= 0:
                continue
            w = 1.0 / sig ** 2
            num += w * Cp; den += w
        if den == 0:
            return None, None
        return num / den, 1.0 / math.sqrt(den)
    Call, SEall = a3(rows)
    wtot = sum(1.0 / ((r["n"] - 1) * r["layer_se_pct"] / 100.0) ** 2 for r in rows
               if r["layer_se_pct"] > 0)
    for r in rows:
        Cp = (r["n"] - 1) * r["layer_pct"] / 100.0
        sig = (r["n"] - 1) * r["layer_se_pct"] / 100.0
        w = 100.0 / sig ** 2 / wtot if sig > 0 else 0.0
        print(f"  {r['p']:>7} {r['layer_pct']:>10.4f} {r['layer_se_pct']:>9.4f} "
              f"{Cp:>10.3f} {w:>9.2f}  {'SEEN' if r['p'] in SEEN else 'UNSEEN'}")
    for label, sub in [("all 10 primes [SEEN-DATA]", rows),
                       ("unseen {211,349,577} only [confirmatory]",
                        [r for r in rows if r["p"] not in SEEN])]:
        C, SEc = a3(sub)
        if C is None:
            continue
        ok = abs(C - A3_C_PRED) <= 3 * SEc and C < 0
        print(f"    {label:<42} C_hat = {C:+.4f} +- {SEc:.4f}   "
              f"|C-Cpred|/SE = {abs(C-A3_C_PRED)/SEc:.2f}   {'PASS' if ok else 'FAIL'}")

    print(f"\n  P-DET-A GATE: {'PASS -- Arm A may issue a verdict' if gate else 'FAIL -- no verdict'}")
    if gate:
        print("  [EMPIRICAL - SEEN-DATA, CONTROL-REPAIRED] per v3 section 0.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", default="163,211,349,433,577,991,2089,4159,9319,19231")
    ap.add_argument("--R", type=int, default=64)
    ap.add_argument("--out", default="row_budget_v3_rows.json")
    ap.add_argument("--seedA", type=int, default=20260801)
    ap.add_argument("--seedB", type=int, default=20260802)
    a = ap.parse_args()
    freqs, h = load_freqs()
    print(f"  frozen frequency list sha256 {h[:24]}...  OK")
    print(f"  streams: A={a.seedA} (verdict replicates)  B={a.seedB} (carriers/plant)")
    rngA = np.random.default_rng(int(a.seedA))
    rngB = np.random.default_rng(int(a.seedB))
    rows = []
    for p in [int(t) for t in a.primes.split(",")]:
        rows.append(run_prime(p, freqs, a.R, rngA, rngB))
        json.dump(rows, open(a.out, "w"), indent=1)
    adjudicate(rows)


if __name__ == "__main__":
    main()
