# semaev_cm_relation_yield_v4.py   --   run:  sage semaev_cm_relation_yield_v4.py [--smoke]
#
# Instrument for PREREG_semaev_cm_relation_yield_v4.md.
# Extends the |V| sweep from v3's {4,5} to {4,5,6,7,8,9}.
# Reuses the frozen instrument semaev_elimination_v1.py (unchanged).
#
# H1 (PRIMARY): matched-#E paired  Delta = logQ_CM - logQ_nonCM(nearest #E), pooled T1, sign-flip null.
# H2 (secondary): R2 = log quo_betaInvV - log quo_randV (mu3_lever_test), sign-flip null (two-sided, ~1).
# Scaling: T1(|V|) fitted to M_flat, M_linear, M_log with AICc + permutation bootstrap.
# C1 plant, C4 negative controls, C6 v3-reproducibility, frozen SHA schedule.

from sage.all import *
import random, sys, math, hashlib, json, time

H = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/semaev_elimination_v1.py"
_g = {'__name__': 'harness_mod'}
exec(open(H).read(), _g)
measure_system      = _g['measure_system']
decomposable_target = _g['decomposable_target']
mu3_lever_test      = _g['mu3_lever_test']

SMOKE = ('--smoke' in sys.argv)

# ------------------------------------------------------------------ schedule
def primes_1mod3(lo, count, cap=100000):
    out = []; p = lo - 1
    while len(out) < count:
        p = int(next_prime(p))
        if p > cap: break
        if p % 3 == 1: out.append(p)
    return out

def build_curves(p, n_noncm, seed):
    F = GF(p); random.seed(seed); cs = []
    for B in range(1, p):
        cs.append(dict(lab='j0', A=0, B=B, order=int(EllipticCurve(F, [0, B]).order()), mu=6, kappa=3)); break
    for A in range(1, p):
        cs.append(dict(lab='j1728', A=A, B=0, order=int(EllipticCurve(F, [A, 0]).order()), mu=4, kappa=2)); break
    got = tries = 0
    while got < n_noncm and tries < 6000:
        tries += 1
        A = random.randrange(1, p); B = random.randrange(1, p)
        if (4*A**3 + 27*B**2) % p == 0: continue
        E = EllipticCurve(F, [A, B]); j = E.j_invariant()
        if j == F(0) or j == F(1728): continue
        cs.append(dict(lab='nonCM', A=A, B=B, order=int(E.order()), mu=2, kappa=1)); got += 1
    return cs

# ------------------------------------------------------------------ quo per cell (with timing)
def cell_quo(p, A, B, m, extra, K, seed0):
    F = GF(p); Dmax = 2**(m-1) + m*(m + extra) + 5; qs = []; t0 = time.time()
    for k in range(K):
        dt = decomposable_target(F, A, B, m, extra=extra, seed=seed0 + k)
        if dt is None: continue
        tval, V = dt
        r = measure_system(F, A, B, m, tval, V, Dmax)
        if r['dim'] == 0 and r['quo'] is not None: qs.append(int(r['quo']))
    elapsed = time.time() - t0
    return qs, elapsed

def logmean(qs):
    return None if not qs else math.log(sum(qs) / len(qs))

def match_nearest(order, curves, used):
    best = bd = None
    for i, c in enumerate(curves):
        if i in used: continue
        d = abs(c['order'] - order)
        if bd is None or d < bd: bd = d; best = i
    return best

def signflip_p(deltas, R=20000, seed=12345, two_sided=False):
    if not deltas: return None, None
    obs = sum(deltas)/len(deltas); random.seed(seed); ge = 0
    for _ in range(R):
        s = sum(d*random.choice((1, -1)) for d in deltas)/len(deltas)
        ge += 1 if ((abs(s) >= abs(obs)-1e-12) if two_sided else (s >= obs-1e-12)) else 0
    return obs, (ge + 1.0)/(R + 1.0)

# ------------------------------------------------------------------ C1 firing plant
def plant_high_quo(p, A, B, m, n_decomps, seed, maxV=7):
    F = GF(p); E = EllipticCurve(F, [A, B]); G = E.gens()[0]; N = int(E.order())
    random.seed(seed); Ptgt = int(random.randrange(1, N))*G
    Vr = set(); made = tries = 0
    while made < n_decomps and tries < 4000 and len(Vr) < maxV:
        tries += 1
        pts = [int(random.randrange(1, N))*G for _ in range(m-1)]
        last = -Ptgt
        for P in pts: last = last - P
        allp = pts + [last]
        if any(P == E(0) for P in allp) or len({tuple(P.xy()) for P in allp}) < m: continue
        newx = {P[0] for P in allp}
        if len(Vr | newx) > maxV: continue
        Vr |= newx; made += 1
    Dmax = 2**(m-1) + m*len(Vr) + 5
    r = measure_system(F, A, B, m, Ptgt[0], list(Vr), Dmax)
    return dict(quo=r['quo'], dim=r['dim'], made=made, sizeV=len(Vr))

# ------------------------------------------------------------------ main run
def run(primes, n_noncm, m, extra, K, tag, sched=None):
    print("=" * 78)
    print("tag=%s  m=%d |V|=%d K=%d  #primes=%d" % (tag, m, m+extra, K, len(primes)))
    dj0 = []; dj17 = []; r2s = []; c4 = []; egaps = []
    cell_times = []
    t_run_start = time.time()
    for p in primes:
        t_p_start = time.time()
        cs = build_curves(p, n_noncm, seed=1000 + p)
        for c in cs:
            qs, elapsed = cell_quo(p, c['A'], c['B'], m, extra, K, seed0=7000)
            c['Q'] = logmean(qs)
            c['n_quo'] = len(qs)
            cell_times.append(elapsed)
        noncm = [c for c in cs if c['lab'] == 'nonCM']
        cj0  = [c for c in cs if c['lab'] == 'j0'][0]
        cj17 = [c for c in cs if c['lab'] == 'j1728'][0]
        if sched is not None:
            sched.append(dict(p=p, curves=[{k: c[k] for k in ('lab','A','B','order','mu','kappa')} for c in cs]))
        used = set()
        i0 = match_nearest(cj0['order'], noncm, used);  used.add(i0)
        i17 = match_nearest(cj17['order'], noncm, used); used.add(i17)
        if cj0['Q'] is not None and noncm[i0]['Q'] is not None:
            dj0.append(cj0['Q'] - noncm[i0]['Q'])
            egaps.append(abs(cj0['order']-noncm[i0]['order'])/float(p))
        if cj17['Q'] is not None and noncm[i17]['Q'] is not None:
            dj17.append(cj17['Q'] - noncm[i17]['Q'])
        # C4 negative control
        rem = [i for i in range(len(noncm)) if i not in (i0, i17) and noncm[i]['Q'] is not None]
        if len(rem) >= 2:
            rem.sort(key=lambda i: noncm[i]['order'])
            c4.append(noncm[rem[0]]['Q'] - noncm[rem[1]]['Q'])
        # H2 mu3 lever (j0 form)
        kk = max(2, (m+extra+2)//3); Dm = 2**(m-1) + m*(3*kk) + 5
        out = mu3_lever_test(p, m, kk, Dm)
        if 'error' not in out:
            qb = out['secp_betaInvV']['quo']; qr = out['secp_randomV']['quo']
            if qb and qr and qb > 0 and qr > 0: r2s.append(math.log(qb) - math.log(qr))
        t_p = time.time() - t_p_start
        print("  p=%-5d T1_j0=%s T1_j1728=%s R2=%s #Egap=%s  [%.1fs]"
              % (p, _f(dj0[-1] if dj0 else None), _f(dj17[-1] if dj17 else None),
                 _f(r2s[-1] if r2s else None), _f(egaps[-1] if egaps else None), t_p))
    print("-" * 50)
    R_perm = 2000 if SMOKE else 20000
    for xs, nm, ts in [(dj0, "T1(j0)   ", False), (dj17, "T1(j1728)", False),
                       (r2s, "R2(mu3)  ", True), (c4, "C4(nonCM)", True)]:
        obs, pv = signflip_p(xs, R=R_perm)
        n = len(xs)
        print("  %s n=%-2d mean=%s  perm_p=%s  (pos %s/%d)"
              % (nm, n, _f(obs), _f(pv), sum(1 for x in xs if x > 0) if xs else 0, n))
    if egaps:
        eg = sorted(egaps); print("  #E-match median rel-gap = %.4f  (C2 cap 2/sqrt(p)~%.4f)"
                                  % (eg[len(eg)//2], 2/math.sqrt(primes[len(primes)//2])))
    t_run = time.time() - t_run_start
    if cell_times:
        print("  [total %.0fs, mean-cell %.2fs, max-cell %.1fs, n_cells=%d]"
              % (t_run, sum(cell_times)/len(cell_times), max(cell_times), len(cell_times)))
    return dict(dj0=dj0, dj17=dj17, r2s=r2s, c4=c4, egaps=egaps, cell_times=cell_times, t_run=t_run)

def _f(x): return "None" if x is None else ("%.4f" % x)

# ------------------------------------------------------------------ Scaling analysis (in-run summary)
def scaling_summary(results_by_V, Vs):
    """Compute T1 per |V|-level and fit flat/linear/log models."""
    print("\n" + "=" * 78)
    print("SCALING ANALYSIS")
    print("=" * 78)
    for cm_label, key in [("j0", "dj0"), ("j1728", "dj17")]:
        print(f"\n  Scaling: {cm_label}")
        pts = []
        for V in Vs:
            V_tag = "V=%d" % V
            if V_tag in results_by_V and results_by_V[V_tag][key]:
                T1_val = sum(results_by_V[V_tag][key]) / len(results_by_V[V_tag][key])
                n = len(results_by_V[V_tag][key])
                pts.append((V, T1_val, n))
                print(f"    |V|={V}: T1={T1_val:.4f}  (n={n})")
        if len(pts) < 3:
            print(f"    (<3 data points, model comparison not possible)")
            continue
        xs = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        ws = [p[2] for p in pts]
        n_pts = len(pts)

        # M_flat: T1 = c
        rss_flat = sum(w * (y - sum(w*y)/sum(w))**2 for w, y in zip(ws, ys))

        # M_linear: T1 = a*|V| + b (weighted LS)
        sw = sum(ws); swx = sum(w*x for w, x in zip(ws, xs))
        swy = sum(w*y for w, y in zip(ws, ys)); swx2 = sum(w*x*x for w, x in zip(ws, xs))
        swxy = sum(w*x*y for w, x, y in zip(ws, xs, ys))
        det = sw * swx2 - swx * swx
        if det != 0:
            a_lin = (sw * swxy - swx * swy) / det
            b_lin = (swy * swx2 - swxy * swx) / det
            rss_lin = sum(w * (y - a_lin * x - b_lin)**2 for w, x, y in zip(ws, xs, ys))
        else:
            a_lin = b_lin = rss_lin = float('nan')

        # M_log: T1 = a*log|V| + b (weighted LS)
        lxs = [math.log(x) for x in xs]
        swlx = sum(w*lx for w, lx in zip(ws, lxs))
        swlx2 = sum(w*lx*lx for w, lx in zip(ws, lxs))
        swlxy = sum(w*lx*y for w, lx, y in zip(ws, lxs, ys))
        det2 = sw * swlx2 - swlx * swlx
        if det2 != 0:
            a_log = (sw * swlxy - swlx * swy) / det2
            b_log = (swy * swlx2 - swlxy * swlx) / det2
            rss_log = sum(w * (y - a_log * lx - b_log)**2 for w, lx, y in zip(ws, lxs, ys))
        else:
            a_log = b_log = rss_log = float('nan')

        # AICc
        def aicc(rss, k_model):
            n = n_pts
            if rss <= 0 or n <= k_model + 1: return float('inf')
            return n * math.log(rss / n) + 2 * k_model + 2 * k_model * (k_model + 1) / (n - k_model - 1)

        aicc_flat = aicc(rss_flat, 1)
        aicc_lin = aicc(rss_lin, 2) if not math.isnan(rss_lin) else float('inf')
        aicc_log = aicc(rss_log, 2) if not math.isnan(rss_log) else float('inf')

        print(f"    RSS(flat)={rss_flat:.6f}  RSS(lin)={rss_lin:.6f}  RSS(log)={rss_log:.6f}")
        print(f"    AICc(flat)={aicc_flat:.2f}  AICc(lin)={aicc_lin:.2f}  AICc(log)={aicc_log:.2f}")
        if aicc_lin < aicc_flat - 6:
            print(f"    >>> LINEAR WINS (delta_AICc={aicc_flat - aicc_lin:.1f})")
        elif aicc_log < aicc_flat - 6:
            print(f"    >>> LOG WINS (delta_AICc={aicc_flat - aicc_log:.1f})")
        elif aicc_flat <= min(aicc_lin, aicc_log) + 2:
            print(f"    >>> FLAT WINS (within delta2 of best growing model)")
        else:
            print(f"    >>> INCONCLUSIVE (no model decisively better)")

        # C6 reproducibility: compare |V|=4,5 to v3 values
        v3_ref = {"j0": {4: 0.2074, 5: 0.4094}, "j1728": {4: 0.1345, 5: 0.2279}}
        if cm_label in v3_ref:
            for V_cmp, T1_ref in v3_ref[cm_label].items():
                obs_pts = [pt for pt in pts if pt[0] == V_cmp]
                if obs_pts:
                    T1_obs = obs_pts[0][1]
                    diff = abs(T1_obs - T1_ref)
                    print(f"    C6 ({cm_label}, |V|={V_cmp}): v3={T1_ref:.4f}  v4={T1_obs:.4f}  diff={diff:.4f}  {'OK' if diff < 0.1 else 'CHECK'}")

if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    print(">>> C1 firing plant (must show quo far above the ~1-6 baseline):")
    pl = plant_high_quo(541, 0, 7, 3, n_decomps=3, seed=5, maxV=7)
    print("    plant: quo=%s dim=%s made=%d sizeV=%d" % (pl['quo'], pl['dim'], pl['made'], pl['sizeV']))

    m = 3
    extras = [1, 2, 3, 4, 5]  # |V| = 4,5,6,7,8 (D1: |V|=9 dropped per smoke-test timing)

    if SMOKE:
        pr = primes_1mod3(500, 3)
        extras_smoke = [3, 4]  # |V|=6,7 only for smoke test
        results_by_V = {}
        for extra in extras_smoke:
            V = m + extra
            tag = "SMOKE-V=%d" % V
            results_by_V[tag] = run(pr, 5, m, extra, 5, tag)
        scaling_summary(results_by_V, [m + e for e in extras_smoke])
    else:
        pr = primes_1mod3(500, 24, cap=8000)
        print("prime schedule: %s" % pr)

        # freeze the schedule BEFORE the first quo
        sched = []
        for p in pr:
            cs = build_curves(p, 5, seed=1000 + p)
            sched.append(dict(p=p, curves=[{k: c[k] for k in ('lab','A','B','order','mu','kappa')} for c in cs]))
        blob = json.dumps(sched, sort_keys=True).encode()
        sha = hashlib.sha256(blob).hexdigest()
        open("_SCHEDULE_semaev_cm_relation_yield_v4.json", "wb").write(blob)
        open("_SCHEDULE_semaev_cm_relation_yield_v4.sha256", "w").write(sha + "\n")
        print("FROZEN schedule SHA-256 (recorded before first quo):", sha)

        results_by_V = {}
        for extra in extras:
            V = m + extra
            tag = "V=%d" % V
            results_by_V[tag] = run(pr, 5, m, extra, 25, tag)

        scaling_summary(results_by_V, [m + e for e in extras])

    print("\n[PROVISIONAL — experiment-designer gate OWED; no grade]")
