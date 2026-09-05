# semaev_cm_relation_yield_v3.py   --   run:  sage semaev_cm_relation_yield_v3.py [--smoke]
#
# Instrument for PREREG_semaev_cm_relation_yield_v3.md.
# Until the experiment-designer v3-delta gate clears (see ..._v3_GATE_OWED_selfaudit.md), any RESULT is
# [PROVISIONAL] and may not be graded.  Exact over GF(p); float only inside rank/permutation statistics.
#
# H1 (PRIMARY): matched-#E paired  Delta = logQ_CM - logQ_nonCM(nearest #E), pooled T1, sign-flip null.
# H2 (mechanism): R2 = log quo_betaInvV - log quo_randV (mu3_lever_test), sign-flip null (two-sided, ~1).
# Scaling: T1 at |V|=4 vs |V|=5.   C1 plant, C4 negative controls, frozen SHA schedule.

from sage.all import *
import random, sys, math, hashlib, json

H = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/semaev_elimination_v1.py"
_g = {'__name__': 'harness_mod'}
exec(open(H).read(), _g)
measure_system      = _g['measure_system']
decomposable_target = _g['decomposable_target']
mu3_lever_test      = _g['mu3_lever_test']

SMOKE = ('--smoke' in sys.argv)
WIDE    = ('--wide' in sys.argv)     # log-spaced primes 500..8000 (addresses DEVIATION D1)
SCALING = ('--scaling' in sys.argv)  # wide primes, |V|=6 only (EXPLORATORY 3rd Scaling point; m=4 infeasible)

# ------------------------------------------------------------------ schedule
def primes_1mod3(lo, count, cap=100000):
    out = []; p = lo - 1
    while len(out) < count:
        p = int(next_prime(p))
        if p > cap: break
        if p % 3 == 1: out.append(p)
    return out

def primes_1mod3_logspaced(lo, hi, count):
    """count primes = 1 mod 3, next-prime above `count` log-spaced anchors in [lo, hi] (dedup, deterministic)."""
    anchors = [int(round(lo * (float(hi)/lo)**(i/float(count-1)))) for i in range(count)]
    out = []
    for a in anchors:
        p = a - 1
        while True:
            p = int(next_prime(p))
            if p % 3 == 1: break
        if p not in out: out.append(p)
    p = max(out)
    while len(out) < count:
        p = int(next_prime(p))
        if p % 3 == 1 and p not in out: out.append(p)
    return sorted(out)

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

# ------------------------------------------------------------------ quo per cell
def cell_quo(p, A, B, m, extra, K, seed0):
    F = GF(p); Dmax = 2**(m-1) + m*(m + extra) + 5; qs = []
    for k in range(K):
        dt = decomposable_target(F, A, B, m, extra=extra, seed=seed0 + k)
        if dt is None: continue
        tval, V = dt
        r = measure_system(F, A, B, m, tval, V, Dmax)
        if r['dim'] == 0 and r['quo'] is not None: qs.append(int(r['quo']))
    return qs

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
    """Factor base seeded with several genuine decompositions of ONE target => inflated quo.
    |V| capped at maxV so the field-equation degree stays tractable."""
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
    for p in primes:
        cs = build_curves(p, n_noncm, seed=1000 + p)
        for c in cs:
            c['Q'] = logmean(cell_quo(p, c['A'], c['B'], m, extra, K, seed0=7000))
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
        # C4 negative control: two nearest-#E non-CM curves (matched) -> Delta should be ~0
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
        print("  p=%-5d T1_j0=%s T1_j1728=%s R2=%s #Egap(j0)=%s"
              % (p, _f(dj0[-1] if dj0 else None), _f(dj17[-1] if dj17 else None),
                 _f(r2s[-1] if r2s else None), _f(egaps[-1] if egaps else None)))
    print("-" * 50)
    for xs, nm, ts in [(dj0, "T1(j0)   ", False), (dj17, "T1(j1728)", False),
                       (r2s, "R2(mu3)  ", True), (c4, "C4(nonCM)", True)]:
        obs, pv = signflip_p(xs, R=(2000 if SMOKE else 20000))
        n = len(xs)
        print("  %s n=%-2d mean=%s  perm_p=%s  (pos %s/%d)"
              % (nm, n, _f(obs), _f(pv), sum(1 for x in xs if x > 0) if xs else 0, n))
    if egaps:
        eg = sorted(egaps); print("  #E-match median rel-gap = %.4f  (C2 cap 2/sqrt(p)~%.4f)"
                                  % (eg[len(eg)//2], 2/math.sqrt(primes[len(primes)//2])))

def _f(x): return "None" if x is None else ("%.4f" % x)

if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    print(">>> C1 firing plant (must show quo far above the ~1-6 baseline):")
    pl = plant_high_quo(541, 0, 7, 3, n_decomps=3, seed=5, maxV=7)
    print("    plant: quo=%s dim=%s made=%d sizeV=%d" % (pl['quo'], pl['dim'], pl['made'], pl['sizeV']))
    if SMOKE:
        run(primes_1mod3(500, 3), 5, 3, 1, 5, "SMOKE-V4")
    else:
        if WIDE or SCALING:
            pr = primes_1mod3_logspaced(500, 8000, 24); sfx = "_v6" if SCALING else "_wide"
        else:
            pr = primes_1mod3(500, 24, cap=8000); sfx = ""
        print("prime schedule (%s): %s"
              % ("WIDE |V|=6 scaling" if SCALING else ("WIDE log-spaced" if WIDE else "first-24"), pr))
        # freeze the schedule (deterministic from the frozen rule) BEFORE the first quo
        sched = []
        for p in pr:
            cs = build_curves(p, 5, seed=1000 + p)
            sched.append(dict(p=p, curves=[{k: c[k] for k in ('lab','A','B','order','mu','kappa')} for c in cs]))
        blob = json.dumps(sched, sort_keys=True).encode()
        sha = hashlib.sha256(blob).hexdigest()
        open("_SCHEDULE_semaev_cm_relation_yield_v3%s.json" % sfx, "wb").write(blob)
        open("_SCHEDULE_semaev_cm_relation_yield_v3%s.sha256" % sfx, "w").write(sha + "\n")
        print("FROZEN schedule SHA-256 (recorded before first quo):", sha)
        if SCALING:
            run(pr, 5, 3, 3, 25, "V=6")   # EXPLORATORY 3rd Scaling point (|V|=6); |V|=4,5 already in the wide run
        else:
            run(pr, 5, 3, 1, 25, "V=4")
            run(pr, 5, 3, 2, 25, "V=5")
    print("[PROVISIONAL — experiment-designer v3-delta gate OWED; no grade]")
