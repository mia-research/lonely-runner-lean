# analysis_capability_v5.py
# Post-run analysis for PREREG_semaev_cm_lever_capability_v5.md.
#   sage analysis_capability_v5.py [--armC10]
#
# Parses:
#   semaev_cm_lever_capability_v5.log  (Arm A summary +, with --armC9/--armC10 runs, Arm C per-prime lines)
#   semaev_mechanism_nt_v5.log         (Arm B per-prime T1 / T1_excess lines + N_T diagnostics)
#   semaev_cm_relation_yield_v4.log    (v4 per-prime lines: the |V|=4..8 baseline for Arm C scaling)
#
# Implements (per prereg §3, prospectively frozen):
#   - C-Scaling model set: M_flat, M_linear, M_log, M_log2 (a·ln|V| + b·(ln|V|)^2 + c)
#   - DUAL weighting: primary weights = per-level n; sensitivity weights = 1/Var(T1) per level
#   - Calibration rule: raw AICc primary (Δ>=6 thresholds), bootstrap stability reported;
#     if the winning verdict's decisive fraction < 0.5 -> [LOW-BOOTSTRAP-SUPPORT] flag
#   - C-stop: |V|=10 arm runs iff T1(9) - T1(8) >= 0.05 (evaluated from the logged V=9 arm)
#
# Plain-Python arithmetic only (no Sage symbolic sum in generators).

import math, random, re, sys

# ---------------------------------------------------------------- log parsing
def parse_per_prime(path, tags=("V=", "ARMC-V=")):
    """Return {V: [per-prime T1_j0 values]} and {V: [per-prime T1_j1728]} from per-prime lines."""
    out_j0 = {}; out_j17 = {}; cur_V = None
    try:
        with open(path) as f:
            lines = f.readlines()
    except FileNotFoundError:
        return out_j0, out_j17
    for line in lines:
        m = re.match(r'tag=(?:SMOKE-)?(?:ARMA-|ARMC-|ARMB-)?V=(\d+)', line)
        if m:
            cur_V = int(m.group(1)); out_j0.setdefault(cur_V, []); out_j17.setdefault(cur_V, [])
            continue
        if cur_V is None:
            continue
        pm = re.match(r'\s+p=(\d+)\s+T1_?j0=([-\d.]+)\s+T1_?j17(?:28)?=([-\d.]+)', line)
        if pm:
            out_j0[cur_V].append(float(pm.group(2)))
            out_j17[cur_V].append(float(pm.group(3)))
    return out_j0, out_j17

def parse_armb(path):
    """Return {V: [(T1, Texcess_j0)]} per-prime and the N_T/#E^2 diagnostic rows."""
    per = {}; diag = []; cur_V = None
    try:
        with open(path) as f:
            lines = f.readlines()
    except FileNotFoundError:
        return per, diag
    for line in lines:
        m = re.match(r'tag=(?:SMOKE-)?ARMB-V=(\d+)', line)
        if m:
            cur_V = int(m.group(1)); per.setdefault(cur_V, []); continue
        if cur_V is None:
            continue
        pm = re.match(r'\s+p=(\d+)\s+T1j0=([-\d.]+)\s+T1j17=\S+\s+Texcess_j0=([-\d.]+)\s+Texcess_j17=\S+', line)
        if pm:
            per[cur_V].append((float(pm.group(2)), float(pm.group(3))))
        dm = re.match(r'\s+p=(\d+)\s+(\S+)\s+#E=(\d+)\s+N_T=(\d+)\s+#E\^2=(\d+)\s+N_T/#E\^2=([\d.]+)', line)
        if dm:
            diag.append((int(dm.group(1)), dm.group(2), int(dm.group(4)), int(dm.group(5)), float(dm.group(6))))
    return per, diag

# ---------------------------------------------------------------- weighted LS (1-d and 2-d designs)
def wls(Xcols, ys, ws):
    """Weighted least squares: Xcols = list of column-vectors (incl. intercept), returns coeffs + RSS."""
    k = len(Xcols); n = len(ys)
    # normal equations
    A = [[0.0] * k for _ in range(k)]; b = [0.0] * k
    for j in range(k):
        for l in range(k):
            s = 0.0
            for i in range(n):
                s += ws[i] * Xcols[j][i] * Xcols[l][i]
            A[j][l] = s
        s = 0.0
        for i in range(n):
            s += ws[i] * Xcols[j][i] * ys[i]
        b[j] = s
    # Gaussian elimination
    for c in range(k):
        piv = max(range(c, k), key=lambda r: abs(A[r][c]))
        if abs(A[piv][c]) < 1e-18:  # noqa: float — (stat) WLS pivot-singularity guard in the AICc C-Scaling regression over measured T1 rates (log-file floats, not exact integers); the model itself uses ln|V| so is inherently float, not a discrete/algebraic decision
            return None, float('nan')
        A[c], A[piv] = A[piv], A[c]; b[c], b[piv] = b[piv], b[c]
        for r in range(c + 1, k):
            f = A[r][c] / A[c][c]
            for cc in range(c, k):
                A[r][cc] -= f * A[c][cc]
            b[r] -= f * b[c]
    coef = [0.0] * k
    for r in range(k - 1, -1, -1):
        s = b[r]
        for cc in range(r + 1, k):
            s -= A[r][cc] * coef[cc]
        coef[r] = s / A[r][r]
    rss = 0.0
    for i in range(n):
        pred = 0.0
        for j in range(k):
            pred += Xcols[j][i] * coef[j]
        rss += ws[i] * (ys[i] - pred) ** 2
    return coef, rss

def aicc(rss, k, n):
    if rss <= 0 or n <= k + 1:
        return float('inf')
    return n * math.log(rss / n) + 2 * k + 2 * k * (k + 1) / (n - k - 1)

def fit_models(xs, ys, ws):
    n = len(xs)
    ones = [1.0] * n
    lns = [math.log(x) for x in xs]
    ln2s = [v * v for v in lns]
    _, rss_flat = wls([ones], ys, ws)
    cl, rss_lin = wls([xs, ones], ys, ws)
    cg, rss_log = wls([lns, ones], ys, ws)
    c2, rss_log2 = wls([lns, ln2s, ones], ys, ws)
    out = dict(
        flat=dict(k=1, rss=rss_flat, aicc=aicc(rss_flat, 1, n)),
        lin=dict(k=2, rss=rss_lin, aicc=aicc(rss_lin, 2, n), coef=cl),
        log=dict(k=2, rss=rss_log, aicc=aicc(rss_log, 2, n), coef=cg),
        log2=dict(k=3, rss=rss_log2, aicc=aicc(rss_log2, 3, n), coef=c2),
    )
    return out

# ---------------------------------------------------------------- main
if __name__ == '__main__':
    inc10 = ('--armC10' in sys.argv)

    # ---- Arm B summary
    print("=" * 78); print("ARM B SUMMARY (mechanism)"); print("=" * 78)
    per, diag = parse_armb("semaev_mechanism_nt_v5.log")
    for V in sorted(per):
        rows = per[V]
        if not rows: continue
        t1 = [r[0] for r in rows]; te = [r[1] for r in rows]
        m1 = sum(t1) / len(t1); m2 = sum(te) / len(te)
        # paired difference between T1 and T1_excess (the normalization effect)
        dm = sum(a - b for a, b in zip(t1, te)) / len(rows)
        print("  |V|=%d: n=%d  T1=%.4f  T1_excess=%.4f  (T1 - T1_excess)=%.4f" % (V, len(rows), m1, m2, dm))
    if diag:
        by_class = {}
        for (p, lab, NT, E2, r) in diag:
            by_class.setdefault(lab, []).append(r)
        print("  N_T/#E^2 by class:")
        for lab, rs in sorted(by_class.items()):
            print("    %-6s mean=%.4f  min=%.4f  max=%.4f  n=%d" % (lab, sum(rs)/len(rs), min(rs), max(rs), len(rs)))

    # ---- Arm C scaling: v4 baseline (V=4..8) + Arm C (V=9, 10)
    print(); print("=" * 78); print("ARM C SCALING (C-Scaling, prereg §3)"); print("=" * 78)
    v4_j0, v4_j17 = parse_per_prime("semaev_cm_relation_yield_v4.log")
    v5_j0, v5_j17 = parse_per_prime("semaev_cm_lever_capability_v5.log")
    levels = {}
    for V in (4, 5, 6, 7, 8):
        if V in v4_j0 and v4_j0[V]:
            levels[V] = v4_j0[V]
    for V in (9, 10):
        src = v5_j0.get(V, [])
        if V == 10 and not inc10:
            continue
        if src:
            levels[V] = src
    Vs = sorted(levels)
    print("  levels:", {V: len(levels[V]) for V in Vs})
    if len(Vs) < 3:
        print("  (insufficient levels; nothing to fit)"); sys.exit(0)

    xs = [float(V) for V in Vs]
    ys = [sum(levels[V]) / len(levels[V]) for V in Vs]
    ns = [float(len(levels[V])) for V in Vs]

    # C-stop evaluation (needs V=9)
    if 9 in levels and 8 in levels:
        inc = ys[Vs.index(9)] - ys[Vs.index(8)]
        print("  C-stop: T1(9)-T1(8) = %+.4f  ->  |V|=10 arm %s" % (inc, "RUNS (>=0.05)" if inc >= 0.05 else "DOES NOT RUN"))

    for wname, ws in [("weights=n (primary)", ns),
                      ("weights=1/Var (sensitivity)", None)]:
        if ws is None:
            vs = []
            for V in Vs:
                vals = levels[V]; mu = sum(vals) / len(vals)
                var = sum((v - mu) ** 2 for v in vals) / max(1, len(vals) - 1)
                vs.append(1.0 / var if var > 0 else 1.0)
            ws = vs
        fits = fit_models(xs, ys, ws)
        print("\n  [%s]" % wname)
        print("    AICc: flat=%.2f  lin=%.2f  log=%.2f  log2=%.2f" %
              (fits['flat']['aicc'], fits['lin']['aicc'], fits['log']['aicc'], fits['log2']['aicc']))
        if fits['log2']['coef']:
            c = fits['log2']['coef']
            print("    log2 fit: T1 = %.4f·ln|V| %+.4f·(ln|V|)² %+.4f  (curvature b=%+.4f)" % (c[0], c[1], c[2], c[1]))
        d_lin = fits['flat']['aicc'] - fits['lin']['aicc']
        d_log = fits['flat']['aicc'] - fits['log']['aicc']
        d_curv = fits['log']['aicc'] - fits['log2']['aicc']
        grows = min(fits['lin']['aicc'], fits['log']['aicc']) < fits['flat']['aicc'] - 6
        if grows and d_curv >= 4 and fits['log2']['coef'][1] < 0:
            verdict = "GROWS-CURVED (saturation onset)"
        elif grows and fits['log']['aicc'] <= fits['lin']['aicc'] and d_curv < 4:
            verdict = "GROWS-LOG"
        elif grows and fits['lin']['aicc'] < fits['log']['aicc']:
            verdict = "GROWS-LINEAR"
        elif fits['flat']['aicc'] <= min(fits['lin']['aicc'], fits['log']['aicc']) + 2:
            verdict = "FLAT"
        else:
            verdict = "INCONCLUSIVE"
        print("    Δ(flat−lin)=%.1f  Δ(flat−log)=%.1f  Δ(log−log2 curvature)=%.1f" % (d_lin, d_log, d_curv))
        print("    >>> verdict candidate: %s" % verdict)

        # bootstrap stability
        if verdict.startswith("GROWS") or verdict == "INCONCLUSIVE":
            random.seed(42); R = 10000; dec = 0; curv = 0
            for _ in range(R):
                bys = []
                for V in Vs:
                    pool = levels[V]
                    smp = [random.choice(pool) for _ in pool]
                    bys.append(sum(smp) / len(smp))
                f2 = fit_models(xs, bys, ns)
                if min(f2['lin']['aicc'], f2['log']['aicc']) < f2['flat']['aicc'] - 6:
                    dec += 1
                    if f2['log']['aicc'] - f2['log2']['aicc'] >= 4 and f2['log2']['coef'][1] < 0:
                        curv += 1
            frac = dec / R
            print("    bootstrap: growth decisive in %.1f%% of resamples (curved: %.1f%%)" % (100 * frac, 100 * curv / R))
            if frac < 0.5:
                print("    >>> [LOW-BOOTSTRAP-SUPPORT] flag REQUIRED on the verdict (decisive fraction < 50%)")

    print("\n[analysis per PREREG v5 §3; verdict routing requires the gate-cleared run log]")
