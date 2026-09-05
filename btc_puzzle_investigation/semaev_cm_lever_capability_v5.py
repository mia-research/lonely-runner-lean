# semaev_cm_lever_capability_v5.py
#   run:  sage semaev_cm_lever_capability_v5.py [--smoke] [--armC9] [--armC10]
#
# PREREG v5, Arm A (cost side) and Arm C (extrapolation).
# Arm A (default): |V| in {4,5,6}, K=15, the v4 24-prime schedule.
#   Logs per cell: quo-vector, d_ff, d_solv, d_gb, elapsed, sum-quo.
#   Verdict-bearing: A-H1 (paired d_solv, two-sided), A-H3 (economics, one-sided).
# Arm C (--armC9): |V|=9, K=10, first 16 primes of the same schedule.
#        (--armC10): |V|=10, K=8, first 12 primes. Run only per the C-stop rule.
#
# PRE-COMMITTED per-cell reduction (frozen before the run):
#   d_solv(cell) := MEDIAN of the per-target d_solv values (lower median on ties,
#   deterministic); same for d_ff, d_gb. Economics cell value := (sum quo)/(elapsed).
#
# Plain-Python arithmetic only (no Sage symbolic sum in generators).

from sage.all import *
import random, sys, math, hashlib, json, time

H = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/semaev_elimination_v1.py"
_g = {'__name__': 'harness_mod'}
exec(open(H).read(), _g)
measure_system      = _g['measure_system']
decomposable_target = _g['decomposable_target']

SMOKE  = ('--smoke' in sys.argv)
ARMC9  = ('--armC9' in sys.argv)
ARMC10 = ('--armC10' in sys.argv)

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

def low_median(xs):
    xs = sorted(xs); n = len(xs)
    return xs[(n - 1) // 2]

# ---------------------------------------------------------------- C1 firing plant (prereg §4)
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

def cell_measure(p, A, B, m, extra, K, seed0):
    """Measure one cell: quo-vector + degree diagnostics + timing."""
    F = GF(p); Dmax = 2**(m-1) + m*(m + extra) + 5
    qs = []; dff = []; dsv = []; dgb = []
    t0 = time.time()
    for k in range(K):
        dt = decomposable_target(F, A, B, m, extra=extra, seed=seed0 + k)
        if dt is None: continue
        tval, V = dt
        r = measure_system(F, A, B, m, tval, V, Dmax)
        if r['dim'] == 0 and r['quo'] is not None:
            qs.append(int(r['quo']))
            if r['d_ff']   is not None: dff.append(int(r['d_ff']))
            if r['d_solv'] is not None: dsv.append(int(r['d_solv']))
            if r['d_gb']   is not None: dgb.append(int(r['d_gb']))
    elapsed = time.time() - t0
    return dict(qs=qs, sum_quo=(sum(qs) if qs else 0), elapsed=elapsed,
                d_ff=(low_median(dff) if dff else None),
                d_solv=(low_median(dsv) if dsv else None),
                d_gb=(low_median(dgb) if dgb else None),
                n_valid=len(qs), n_dsolv=len(dsv))

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
    obs = sum(deltas) / len(deltas); random.seed(seed); ge = 0
    for _ in range(R):
        s = 0.0
        for d in deltas:
            s += d * random.choice((1, -1))
        s /= len(deltas)
        if (abs(s) >= abs(obs) - 1e-12) if two_sided else (s >= obs - 1e-12):
            ge += 1
    return obs, (ge + 1.0) / (R + 1.0)

V4_REF = {  # C6 reference: v4 T1 at K=25 (Arm A uses K=15 = first 15 of same stream)
    "j0":    {4: 0.2074, 5: 0.4094, 6: 0.5668},
    "j1728": {4: 0.1345, 5: 0.2286, 6: 0.3016},
}

def run(primes, n_noncm, m, extra, K, tag):
    print("=" * 78)
    print("tag=%s  m=%d |V|=%d K=%d  #primes=%d" % (tag, m, m + extra, K, len(primes)))
    recs = dict(dj0=[], dj17=[], econ_j0=[], econ_j17=[],
                ddsv_j0=[], ddsv_j17=[], ddff_j0=[], ddff_j17=[],
                cdgb_j0=[], cdgb_j17=[], egaps=[], dsolv_vals=[], cell_times=[], c4=[])
    t_run = time.time()
    for p in primes:
        t_p = time.time()
        cs = build_curves(p, n_noncm, seed=1000 + p)
        for c in cs:
            cm = cell_measure(p, c['A'], c['B'], m, extra, K, seed0=7000)
            c.update(cm)
            recs['dsolv_vals'].append((c['lab'], cm['d_solv']))
            recs['cell_times'].append(cm['elapsed'])
        noncm = [c for c in cs if c['lab'] == 'nonCM']
        cj0  = [c for c in cs if c['lab'] == 'j0'][0]
        cj17 = [c for c in cs if c['lab'] == 'j1728'][0]
        used = set()
        i0 = match_nearest(cj0['order'], noncm, used);  used.add(i0)
        i17 = match_nearest(cj17['order'], noncm, used); used.add(i17)
        if cj0['qs'] and noncm[i0]['qs']:
            recs['dj0'].append(logmean(cj0['qs']) - logmean(noncm[i0]['qs']))
            recs['egaps'].append(abs(cj0['order'] - noncm[i0]['order']) / float(p))
        if cj17['qs'] and noncm[i17]['qs']:
            recs['dj17'].append(logmean(cj17['qs']) - logmean(noncm[i17]['qs']))
        # A-H1: paired d_solv (and diagnostics)
        for ccm, inm, dkey in [(cj0, i0, 'ddsv_j0'), (cj17, i17, 'ddsv_j17')]:
            if ccm['d_solv'] is not None and noncm[inm]['d_solv'] is not None:
                recs[dkey].append(ccm['d_solv'] - noncm[inm]['d_solv'])
        for ccm, inm, dkey in [(cj0, i0, 'ddff_j0'), (cj17, i17, 'ddff_j17')]:
            if ccm['d_ff'] is not None and noncm[inm]['d_ff'] is not None:
                recs[dkey].append(ccm['d_ff'] - noncm[inm]['d_ff'])
        for ccm, inm, dkey in [(cj0, i0, 'cdgb_j0'), (cj17, i17, 'cdgb_j17')]:
            if ccm['d_gb'] is not None and noncm[inm]['d_gb'] is not None:
                recs[dkey].append(ccm['d_gb'] - noncm[inm]['d_gb'])
        # A-H3: economics (sum quo / elapsed), paired log-ratio
        for ccm, inm, ekey in [(cj0, i0, 'econ_j0'), (cj17, i17, 'econ_j17')]:
            ec = ccm['sum_quo'] / ccm['elapsed'] if ccm['elapsed'] > 0 else 0.0
            en = noncm[inm]['sum_quo'] / noncm[inm]['elapsed'] if noncm[inm]['elapsed'] > 0 else 0.0
            if ec > 0 and en > 0:
                recs[ekey].append(math.log(ec / en))
        # C4 negative control: nonCM vs nonCM (adjacent-pair by #E)
        rem = [i for i in range(len(noncm)) if i not in (i0, i17) and noncm[i]['qs']]
        if len(rem) >= 2:
            rem.sort(key=lambda i: noncm[i]['order'])
            q0 = logmean(noncm[rem[0]]['qs'])
            q1 = logmean(noncm[rem[1]]['qs'])
            if q0 is not None and q1 is not None:
                recs['c4'].append(q0 - q1)
        t_el = time.time() - t_p
        print("  p=%-5d T1j0=%s T1j17=%s dsv(j0)=%s/%s dsv(j17)=%s/%s econj0=%s econj17=%s [%.1fs]"
              % (p, _f(recs['dj0'][-1] if recs['dj0'] else None),
                 _f(recs['dj17'][-1] if recs['dj17'] else None),
                 cj0['d_solv'], noncm[i0]['d_solv'], cj17['d_solv'], noncm[i17]['d_solv'],
                 _f(recs['econ_j0'][-1] if recs['econ_j0'] else None),
                 _f(recs['econ_j17'][-1] if recs['econ_j17'] else None), t_el))
    print("-" * 50)
    Rp = 2000 if SMOKE else 20000
    tests = [
        ("T1(j0)   ", recs['dj0'],    False), ("T1(j1728)", recs['dj17'],   False),
        ("d_solv j0", recs['ddsv_j0'], True), ("d_solv j17", recs['ddsv_j17'], True),
        ("d_ff  j0 ", recs['ddff_j0'], True), ("d_ff  j17 ", recs['ddff_j17'], True),
        ("d_gb  j0 ", recs['cdgb_j0'], True), ("d_gb  j17 ", recs['cdgb_j17'], True),
        ("econ  j0 ", recs['econ_j0'], False), ("econ  j17 ", recs['econ_j17'], False),
        ("C4(nonCM)", recs['c4'], True),
    ]
    for nm, xs, two in tests:
        obs, pv = signflip_p(xs, R=Rp, two_sided=two)
        n = len(xs) if xs else 0
        pos = 0
        if xs:
            for x in xs:
                if x > 0: pos += 1
        print("  %-10s n=%-2d mean=%s  perm_p=%s  (pos %d/%d)"
              % (nm, n, _f(obs), _f(pv), pos, n))
    # C8: d_solv distribution
    dsv_all = [v for (_, v) in recs['dsolv_vals'] if v is not None]
    if dsv_all:
        cnt = {}
        for v in dsv_all:
            cnt[v] = cnt.get(v, 0) + 1
        print("  C8 d_solv distribution:", dict(sorted(cnt.items())))
    if recs['egaps']:
        eg = sorted(recs['egaps'])
        print("  #E-match median rel-gap = %.4f  (cap 2/sqrt(p)~%.4f)"
              % (eg[len(eg) // 2], 2 / math.sqrt(primes[len(primes) // 2])))
    # C6 (Arm A only, |V| in ref)
    V = m + extra
    for lab, dkey in [("j0", 'dj0'), ("j1728", 'dj17')]:
        if V in V4_REF.get(lab, {}) and recs[dkey]:
            mu = sum(recs[dkey]) / len(recs[dkey])
            sd = 0.0
            for x in recs[dkey]:
                sd += (x - mu) ** 2
            sd = math.sqrt(sd / max(1, len(recs[dkey]) - 1)) / math.sqrt(len(recs[dkey]))
            ref = V4_REF[lab][V]
            z = abs(mu - ref) / sd if sd > 0 else float('inf')
            print("  C6 %s |V|=%d: v4=%.4f v5=%.4f  z=%.1f  [%s]"
                  % (lab, V, ref, mu, z, "PASS" if z < 2 else "CHECK"))
    print("  [total %.0fs]" % (time.time() - t_run))
    return recs

def _f(x): return "None" if x is None else ("%+.4f" % x)

if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    print(">>> C1 firing plant (must show quo far above the ~1-6 baseline):")
    pl = plant_high_quo(541, 0, 7, 3, n_decomps=3, seed=5, maxV=7)
    print("    plant: quo=%s dim=%s made=%d sizeV=%d" % (pl['quo'], pl['dim'], pl['made'], pl['sizeV']))
    m = 3
    if ARMC9 or ARMC10:
        full = primes_1mod3(500, 24, cap=8000)
        if ARMC9:
            pr = full[:16]; extra = 6; K = 10; tag = "ARMC-V=9"
        else:
            pr = full[:12]; extra = 7; K = 8; tag = "ARMC-V=10"
        # freeze schedule
        sched = []
        for p in pr:
            cs = build_curves(p, 5, seed=1000 + p)
            sched.append(dict(p=p, curves=[{k: c[k] for k in ('lab', 'A', 'B', 'order', 'mu', 'kappa')} for c in cs]))
        blob = json.dumps(sched, sort_keys=True).encode()
        sha = hashlib.sha256(blob).hexdigest()
        open("_SCHEDULE_v5_C.json", "wb").write(blob)
        open("_SCHEDULE_v5_C.sha256", "w").write(sha + "\n")
        print("FROZEN Arm C schedule SHA-256 (before first quo):", sha)
        run(pr, 5, m, extra, K, tag)
    elif SMOKE:
        pr = primes_1mod3(500, 3)
        run(pr, 5, m, 3, 5, "SMOKE-A-V=6")
    else:
        pr = primes_1mod3(500, 24, cap=8000)
        sched = []
        for p in pr:
            cs = build_curves(p, 5, seed=1000 + p)
            sched.append(dict(p=p, curves=[{k: c[k] for k in ('lab', 'A', 'B', 'order', 'mu', 'kappa')} for c in cs]))
        blob = json.dumps(sched, sort_keys=True).encode()
        sha = hashlib.sha256(blob).hexdigest()
        open("_SCHEDULE_v5_A.json", "wb").write(blob)
        open("_SCHEDULE_v5_A.sha256", "w").write(sha + "\n")
        print("FROZEN Arm A schedule SHA-256 (before first quo):", sha)
        for extra in (1, 2, 3):
            run(pr, 5, m, extra, 15, "ARMA-V=%d" % (m + extra))
    print("\n[PROVISIONAL — experiment-designer gate on PREREG v5 OWED before grading]")
