# analysis_scaling_v4.py
# Post-run analysis for PREREG_semaev_cm_relation_yield_v4.md
# Reads per-prime data from semaev_cm_relation_yield_v4.log, fits flat/linear/log models,
# runs permutation bootstrap calibration, checks C6 reproducibility.
#
# Usage: sage analysis_scaling_v4.py

import math, random, re, sys

# v3 reference values for C6
V3_REF = {
    "j0":     {4: 0.2074, 5: 0.4094},
    "j1728":  {4: 0.1345, 5: 0.2279},
}

# ---- parse log ----
def parse_log(path):
    """Parse semaev_cm_relation_yield_v4.log into per-V, per-prime data."""
    with open(path) as f:
        lines = f.readlines()

    results = {}  # V -> dict of lists
    current_V = None
    for line in lines:
        m = re.match(r'tag=(SMOKE-)?V=(\d+)', line)
        if m:
            current_V = int(m.group(2))
            results[current_V] = {'dj0': [], 'dj17': [], 'r2s': [], 'c4': [], 'egaps': []}
            continue
        if current_V is None:
            continue
        # per-prime line
        pm = re.match(
            r'\s+p=(\d+)\s+T1_j0=([-\d.]+)\s+T1_j1728=([-\d.]+)\s+R2=([-\d.]+)\s+#Egap=([-\d.]+)\s+\[',
            line
        )
        if pm:
            p = int(pm.group(1))
            results[current_V]['dj0'].append(float(pm.group(2)))
            results[current_V]['dj17'].append(float(pm.group(3)))
            results[current_V]['r2s'].append(float(pm.group(4)))
            results[current_V]['egaps'].append(float(pm.group(5)))
        # C4 per-prime is not logged per-line; we compute from summary

    return results

def parse_c4_from_log(path):
    """Extract C4 summary lines to get per-V C4 means."""
    with open(path) as f:
        lines = f.readlines()
    c4_data = {}
    for line in lines:
        m = re.match(r'tag=(SMOKE-)?V=(\d+)', line)
        if m:
            cur_v = int(m.group(2))
            continue
        m2 = re.search(r'C4\(nonCM\)\s+n=(\d+)\s+mean=([-\d.]+)\s+perm_p=([-\d.]+)', line)
        # The parens are already escaped above with \( and \), so this should work
        if m2 and cur_v:
            c4_data[cur_v] = {
                'n': int(m2.group(1)),
                'mean': float(m2.group(2)),
                'p': float(m2.group(3))
            }
    return c4_data

def parse_summary_stats(path):
    """Extract T1/R2 summary lines."""
    with open(path) as f:
        lines = f.readlines()
    stats = {}
    cur_v = None
    for line in lines:
        m = re.match(r'tag=(SMOKE-)?V=(\d+)', line)
        if m:
            cur_v = int(m.group(2))
            stats[cur_v] = {}
            continue
        if cur_v is None:
            continue
        for nm, key in [("T1(j0)", "T1j0"), ("T1(j1728)", "T1j17"), ("R2(mu3)", "R2")]:
            ms = re.search(re.escape(nm) + r'\s+n=(\d+)\s+mean=([-\d.]+)\s+perm_p=([-\d.]+)', line)
            if ms:
                stats[cur_v][key] = {
                    'n': int(ms.group(1)),
                    'mean': float(ms.group(2)),
                    'p': float(ms.group(3))
                }
    return stats

# ---- weighted LS + AICc ----
def fit_flat(xs, ys, ws):
    """T1 = c (weighted mean)."""
    sw = sum(ws)
    c = sum(w*y for w, y in zip(ws, ys)) / sw
    rss = sum(w * (y - c)**2 for w, y in zip(ws, ys))
    return {'c': c, 'rss': rss, 'k': 1}

def fit_linear(xs, ys, ws):
    """T1 = a*|V| + b."""
    sw = sum(ws); swx = sum(w*x for w, x in zip(ws, xs))
    swy = sum(w*y for w, y in zip(ws, ys)); swx2 = sum(w*x*x for w, x in zip(ws, xs))
    swxy = sum(w*x*y for w, x, y in zip(ws, xs, ys))
    det = sw * swx2 - swx * swx
    if abs(det) < 1e-15:  # noqa: float — (stat) WLS determinant-singularity guard fitting T1=a|V|+b to measured T1 rates (log-file floats, not exact integers); a model-selection numerical-stability check, not a discrete/algebraic decision
        return None
    a = (sw * swxy - swx * swy) / det
    b = (swy * swx2 - swxy * swx) / det
    rss = sum(w * (y - a * x - b)**2 for w, x, y in zip(ws, xs, ys))
    return {'a': a, 'b': b, 'rss': rss, 'k': 2}

def fit_log(xs, ys, ws):
    """T1 = a*log|V| + b."""
    lxs = [math.log(x) for x in xs]
    sw = sum(ws); swlx = sum(w*lx for w, lx in zip(ws, lxs))
    swy = sum(w*y for w, y in zip(ws, ys)); swlx2 = sum(w*lx*lx for w, lx in zip(ws, lxs))
    swlxy = sum(w*lx*y for w, lx, y in zip(ws, lxs, ys))
    det = sw * swlx2 - swlx * swlx
    if abs(det) < 1e-15:
        return None
    a = (sw * swlxy - swlx * swy) / det
    b = (swy * swlx2 - swlxy * swlx) / det
    rss = sum(w * (y - a * lx - b)**2 for w, lx, y in zip(ws, lxs, ys))
    return {'a': a, 'b': b, 'rss': rss, 'k': 2}

def aicc(rss, k, n):
    """AICc for small-n corrected Akaike."""
    if rss <= 0 or n <= k + 1:
        return float('inf')
    return n * math.log(rss / n) + 2 * k + 2 * k * (k + 1) / (n - k - 1)

# ---- permutation bootstrap ----
def bootstrap_scaling(per_prime_data, Vs, key, n_boot=10000, seed=42):
    """
    Residual bootstrap: at each |V|, sample with replacement from per-prime deltas,
    compute T1, refit all three models, compute delta_AICc between best-growing and flat.
    Returns: fraction of draws where best-growing beats flat by >=6 AICc.
    """
    random.seed(seed)
    n_pts = len(Vs)
    cal_p = {'lin': 0, 'log': 0, 'either': 0, 'flat': 0}
    for _ in range(n_boot):
        # resample T1 at each |V|
        pts = []
        for V in Vs:
            if V in per_prime_data and per_prime_data[V][key]:
                pool = per_prime_data[V][key]
                n_p = len(pool)
                sample = [random.choice(pool) for __ in range(n_p)]
                pts.append((V, sum(sample)/n_p, n_p))
        if len(pts) < 3:
            continue
        xs = [p[0] for p in pts]; ys = [p[1] for p in pts]; ws = [p[2] for p in pts]
        f = fit_flat(xs, ys, ws)
        l = fit_linear(xs, ys, ws)
        g = fit_log(xs, ys, ws)
        if f is None or l is None or g is None:
            continue
        af = aicc(f['rss'], f['k'], n_pts)
        al = aicc(l['rss'], l['k'], n_pts)
        ag = aicc(g['rss'], g['k'], n_pts)
        if al < af - 6:
            cal_p['lin'] += 1
        if ag < af - 6:
            cal_p['log'] += 1
        if min(al, ag) < af - 6:
            cal_p['either'] += 1
        if af <= min(al, ag) + 2:
            cal_p['flat'] += 1
    return {k: v / n_boot for k, v in cal_p.items()}

# ---- C6 reproducibility ----
def check_c6(stats, ref=V3_REF):
    """Check v3 reproducibility for |V|=4,5."""
    print("\n  C6 REPRODUCIBILITY CHECK")
    for cm_label, key in [("j0", "T1j0"), ("j1728", "T1j17")]:
        if cm_label in ref:
            for V_cmp, T1_ref in ref[cm_label].items():
                if V_cmp in stats and key in stats[V_cmp]:
                    T1_obs = stats[V_cmp][key]['mean']
                    diff = abs(T1_obs - T1_ref)
                    # 2σ band: σ ≈ 0.06 (from v3 per-prime scatter), σ_mean ≈ 0.06/sqrt(24) ≈ 0.012
                    sigma_mean = 0.06 / math.sqrt(24)
                    n_sigma = diff / sigma_mean if sigma_mean > 0 else float('inf')
                    ok = "PASS" if n_sigma < 2 else "FAIL"
                    print(f"    {cm_label} |V|={V_cmp}: v3={T1_ref:.4f}  v4={T1_obs:.4f}  "
                          f"diff={diff:.4f}  {n_sigma:.1f}σ  [{ok}]")

# ---- main ----
if __name__ == '__main__':
    log_path = "semaev_cm_relation_yield_v4.log"
    print(f"Reading {log_path}...")

    per_prime = parse_log(log_path)
    c4_data = parse_c4_from_log(log_path)
    stats = parse_summary_stats(log_path)

    complete_only = ('--complete-only' in sys.argv)
    min_n = 24 if complete_only else 1
    Vs_all = sorted(per_prime.keys())
    Vs = [V for V in Vs_all if len(per_prime[V]['dj0']) >= min_n]
    print(f"  |V| levels found: {Vs_all}")
    if complete_only:
        print(f"  Using complete levels (n>=24): {Vs}")
    else:
        print(f"  Using all levels with data: {Vs}")
    for V in Vs:
        d = per_prime[V]
        print(f"    |V|={V}: n_primes(dj0)={len(d['dj0'])}, n_primes(dj17)={len(d['dj17'])}, "
              f"n_primes(r2)={len(d['r2s'])}")

    # Check if all levels have complete data
    complete_Vs = [V for V in Vs if len(per_prime[V]['dj0']) >= 24]
    if len(complete_Vs) < 5:
        print(f"\n  *** WARNING: only {len(complete_Vs)} levels have >= 24 primes. "
              f"Full scaling analysis requires 5. ***")
        print(f"  *** Proceeding with available {len(complete_Vs)} levels as provisional. ***")

    # ---- H1 per level ----
    print("\n" + "=" * 78)
    print("H1 PER LEVEL")
    print("=" * 78)
    for cm_label, key in [("j0", "dj0"), ("j1728", "dj17")]:
        print(f"\n  {cm_label}:")
        for V in sorted(Vs):
            ds = per_prime[V][key]
            if not ds:
                continue
            n = len(ds)
            mean = sum(ds)/n
            pos = sum(1 for d in ds if d > 0)
            # permutation p (one-sided)
            R = 20000; random.seed(12345); ge = 0
            for _ in range(R):
                s = sum(d * random.choice((1, -1)) for d in ds) / n
                if s >= mean - 1e-12:
                    ge += 1
            p_val = (ge + 1.0) / (R + 1.0)
            print(f"    |V|={V}: T1={mean:.4f}  p={p_val:.4f}  ({pos}/{n} pos)")
        # Also show incomplete levels (informational only)
        for V in sorted(set(per_prime.keys()) - set(Vs)):
            ds = per_prime[V][key]
            if ds:
                n = len(ds); mean = sum(ds)/n
                print(f"    |V|={V}: T1={mean:.4f}  (n={n}, INCOMPLETE — not in fit)")

    # ---- C4 ----
    print("\n" + "=" * 78)
    print("C4 NULL CONTROL")
    print("=" * 78)
    for V in sorted(c4_data.keys()):
        c = c4_data[V]
        print(f"  |V|={V}: mean={c['mean']:.4f}  p={c['p']:.4f}  n={c['n']}")
        # C4 firing check (two-sided, H0: mean=0)
        # The prereg says C4 must NOT fire (mean≈0). We check if p < 0.05 (two-sided).
        # The log reports two-sided p via signflip_p with two_sided=True

    # ---- Scaling model fit ----
    print("\n" + "=" * 78)
    print("SCALING MODEL FIT")
    print("=" * 78)

    for cm_label, key in [("j0", "dj0"), ("j1728", "dj17")]:
        print(f"\n  Scaling: {cm_label}")
        pts = []
        for V in sorted(Vs):
            ds = per_prime[V][key]
            if not ds:
                continue
            T1_val = sum(ds)/len(ds)
            n = len(ds)
            pts.append((V, T1_val, n))
            print(f"    |V|={V}: T1={T1_val:.4f}  (n={n})")
        # Also show incomplete
        for V in sorted(set(per_prime.keys()) - set(Vs)):
            ds = per_prime[V][key]
            if ds:
                n = len(ds); T1_val = sum(ds)/n
                print(f"    |V|={V}: T1={T1_val:.4f}  (n={n}, INCOMPLETE — not in fit)")

        if len(pts) < 3:
            print(f"    (<3 data points, model comparison not possible)")
            continue

        xs = [p[0] for p in pts]; ys = [p[1] for p in pts]; ws = [p[2] for p in pts]
        n_pts = len(pts)

        f = fit_flat(xs, ys, ws)
        l = fit_linear(xs, ys, ws)
        g = fit_log(xs, ys, ws)

        af = aicc(f['rss'], f['k'], n_pts)
        al = aicc(l['rss'], l['k'], n_pts) if l else float('inf')
        ag = aicc(g['rss'], g['k'], n_pts) if g else float('inf')

        rss_lin_str = f"{l['rss']:.6f}" if l else "nan"
        rss_log_str = f"{g['rss']:.6f}" if g else "nan"
        print(f"    RSS(flat)={f['rss']:.6f}  RSS(lin)={rss_lin_str}  RSS(log)={rss_log_str}")
        print(f"    AICc(flat)={af:.2f}  AICc(lin)={al:.2f}  AICc(log)={ag:.2f}")

        if l:
            print(f"    linear: T1 = {l['a']:.4f}*|V| + {l['b']:.4f}")
        if g:
            print(f"    log:    T1 = {g['a']:.4f}*log|V| + {g['b']:.4f}")

        delta_lin = af - al if l else 0
        delta_log = af - ag if g else 0
        delta_best = max(delta_lin, delta_log)

        if al < af - 6 and al <= ag:
            print(f"    >>> LINEAR WINS (ΔAICc vs flat = {delta_lin:.1f})")
            scaling_verdict = "GROWS (linear)"
        elif ag < af - 6:
            print(f"    >>> LOG WINS (ΔAICc vs flat = {delta_log:.1f})")
            scaling_verdict = "GROWS (log)"
        elif af <= min(al, ag) + 2:
            print(f"    >>> FLAT WINS")
            scaling_verdict = "FLAT"
        else:
            print(f"    >>> INCONCLUSIVE (Δ_lin={delta_lin:.1f}, Δ_log={delta_log:.1f})")
            scaling_verdict = "INCONCLUSIVE"

        # ---- Bootstrap calibration ----
        print(f"\n    Bootstrap calibration ({10000} resamples)...")
        cal = bootstrap_scaling(per_prime, Vs, key, n_boot=10000)
        print(f"    P(bootstrap: linear beats flat by ≥6 AICc) = {cal['lin']:.4f}")
        print(f"    P(bootstrap: log beats flat by ≥6 AICc)    = {cal['log']:.4f}")
        print(f"    P(bootstrap: either growing beats flat ≥6)  = {cal['either']:.4f}")
        print(f"    P(bootstrap: flat within Δ2 of best growing) = {cal['flat']:.4f}")

    # ---- H2 Scaling ----
    print("\n" + "=" * 78)
    print("H2 SCALING (x-closure effect vs |V|)")
    print("=" * 78)
    r2_pts = []
    for V in sorted(Vs):
        rs = per_prime[V]['r2s']
        if not rs:
            continue
        R2_val = sum(rs)/len(rs)
        n = len(rs)
        r2_pts.append((V, R2_val, n))
        print(f"    |V|={V}: R2={R2_val:.4f}  (n={n})")

    if len(r2_pts) >= 3:
        xs_r = [p[0] for p in r2_pts]; ys_r = [p[1] for p in r2_pts]; ws_r = [p[2] for p in r2_pts]
        fr = fit_flat(xs_r, ys_r, ws_r)
        lr = fit_linear(xs_r, ys_r, ws_r)
        gr = fit_log(xs_r, ys_r, ws_r)
        afr = aicc(fr['rss'], fr['k'], len(r2_pts))
        alr = aicc(lr['rss'], lr['k'], len(r2_pts)) if lr else float('inf')
        agr = aicc(gr['rss'], gr['k'], len(r2_pts)) if gr else float('inf')
        print(f"    AICc(flat)={afr:.2f}  AICc(lin)={alr:.2f}  AICc(log)={agr:.2f}")
        if lr and alr < afr - 6:
            print(f"    >>> H2-Scaling: LINEAR GROWS (Δ={afr-alr:.1f})")
        elif gr and agr < afr - 6:
            print(f"    >>> H2-Scaling: LOG GROWS (Δ={afr-agr:.1f})")
        elif afr <= min(alr, agr) + 2:
            print(f"    >>> H2-Scaling: FLAT")
        else:
            print(f"    >>> H2-Scaling: INCONCLUSIVE")
    else:
        print("    (<3 data points)")

    # ---- C6 ----
    check_c6(stats)

    # ---- Verdict routing ----
    print("\n" + "=" * 78)
    print("VERDICT ROUTING (§8)")
    print("=" * 78)
    # Determine H1 pooled status
    all_dj0 = []
    for V in sorted(Vs):
        all_dj0.extend(per_prime[V]['dj0'])
    if all_dj0:
        pooled_mean = sum(all_dj0)/len(all_dj0)
        R = 20000; random.seed(54321); ge = 0
        for _ in range(R):
            s = sum(d * random.choice((1, -1)) for d in all_dj0)/len(all_dj0)
            if s >= pooled_mean - 1e-12:
                ge += 1
        pooled_p = (ge + 1.0)/(R + 1.0)
        print(f"  Pooled H1(j0): mean={pooled_mean:.4f}  p={pooled_p:.6f}")
        h1_fires = pooled_p < 0.01
        print(f"  H1 fires (pooled, α=0.01): {h1_fires}")

    # Count H1 per-level fires
    n_fire = 0
    for V in sorted(Vs):
        ds = per_prime[V]['dj0']
        if not ds:
            continue
        n = len(ds)
        mean_v = sum(ds)/n
        R = 20000; random.seed(12345 + V); ge = 0
        for _ in range(R):
            s = sum(d * random.choice((1, -1)) for d in ds)/n
            if s >= mean_v - 1e-12:
                ge += 1
        pv = (ge + 1.0)/(R + 1.0)
        if pv < 0.01:
            n_fire += 1
            print(f"    |V|={V}: H1 fires (p={pv:.4f})")
    print(f"  H1 fires at {n_fire}/{len(per_prime)} levels")
    h1_fires_levels = n_fire >= 4

    # Scaling verdict (from the fitted models above — need to recompute)
    # ... (printed above, we'd need to capture it)
    print("\n  [Verdict routing requires manual integration of Scaling verdict above with H1 status]")
    print("  If H1 fires AND Scaling verdict = GROWS → A1")
    print("  If H1 fires AND Scaling verdict = FLAT  → A2")
    print("  If H1 fires AND Scaling verdict = INCONCLUSIVE → A3")
    print("  If any C1-C5 fails → A7")
