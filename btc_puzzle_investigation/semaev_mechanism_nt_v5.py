# semaev_mechanism_nt_v5.py   --   run:  sage semaev_mechanism_nt_v5.py [--smoke]
#
# PREREG v5, Arm B (mechanism): N_T normalization of the CM yield lever.
#
# Per (curve, target):  N_T = #{(x1,x2,x3) in F_p^3 : S_4(x1,x2,x3,x_T) = 0}
#   computed EXACTLY by vectorized brute force over F_p^3 (numpy int64 modular
#   arithmetic; every intermediate < 13 * p^2 << 2^63, so exact for p < 2^31).
#   Evaluation factored by the x1-exponent: S = sum_{e1} x1^e1 * G_{e1}(x2,x3);
#   the bivariate grids G_{e1} are built once per (curve,target), then swept over u = x1.
# Per cell: quo from the FROZEN instrument (K=10 targets).
# Normalized excess per target:  E = quo * p^3 / (|V|^3 * N_T)   (uniform-random-V model: E ~ 1)
# Verdict-bearing: B-H1  T1_excess = paired mean(log E_CM - log E_nonCM), two-sided sign-flip.
# C7 cross-check: at 2 primes, one target's N_T recomputed with x3-outer factorization;
#   exact integer equality required.

from sage.all import *
import random, sys, math, hashlib, json, time
import numpy as np

H = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/semaev_elimination_v1.py"
_g = {'__name__': 'harness_mod'}
exec(open(H).read(), _g)
measure_system      = _g['measure_system']
decomposable_target = _g['decomposable_target']
summation_poly      = _g['summation_poly']

SMOKE = ('--smoke' in sys.argv)

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

# ---------------------------------------------------------------- exact S4 extraction
def s4_monomials(p, A, B, tval):
    """S_4(x1,x2,x3,tval) over F_p from the FROZEN instrument construction.
    Returns list of (e1, e2, e3, c) with c in [0, p)."""
    F = GF(p)
    S, zs, t = summation_poly(F, A, B, 3)          # S in z1,z2,z3,t
    Rt = zs[0].parent()
    R3 = PolynomialRing(F, ['x1', 'x2', 'x3'])
    phi = Rt.hom(list(R3.gens()) + [F(tval)], R3)
    S3v = phi(S)
    out = []
    for mono, cf in S3v.dict().items():
        c = int(cf) % p
        if c:
            out.append((int(mono[0]), int(mono[1]), int(mono[2]), c))
    return out

def n_t_bruteforce(p, monos, axis=0):
    """Exact count of F_p^3 zeros. axis selects the factoring variable (0 -> x1, 2 -> x3)."""
    if axis == 0:
        e_a = [m[0] for m in monos]; e_b = [m[1] for m in monos]; e_c = [m[2] for m in monos]
    else:  # axis = 2: factor by x3 exponent, grids over (x1,x2)
        e_a = [m[2] for m in monos]; e_b = [m[0] for m in monos]; e_c = [m[1] for m in monos]
    Eset = sorted(set(e_a))
    P = int(p)
    xb = np.arange(P, dtype=np.int64); xc = np.arange(P, dtype=np.int64)
    # grids G_ea[xb, xc] = sum over monos with that ea of c * x_b^eb * x_c^ec   (mod p)
    grids = {ea: np.zeros((P, P), dtype=np.int64) for ea in Eset}
    for (ea, eb, ec, c) in zip(e_a, e_b, e_c, [m[3] for m in monos]):
        if axis == 0:
            pb = np.power.outer(xb, eb) if eb > 0 else np.ones(P, dtype=np.int64)
            pc = np.power.outer(xc, ec) if ec > 0 else np.ones(P, dtype=np.int64)
            grids[ea] = (grids[ea] + int(c) * np.multiply.outer(pb, pc)) % P
        else:
            pb = np.power.outer(xb, eb) if eb > 0 else np.ones(P, dtype=np.int64)
            pc = np.power.outer(xc, ec) if ec > 0 else np.ones(P, dtype=np.int64)
            grids[ea] = (grids[ea] + int(c) * np.multiply.outer(pb, pc)) % P
    # sweep the factored variable u; count grid zeros of sum_ea u^ea * G_ea
    N = 0
    gl = [grids[ea] for ea in Eset]
    for u in range(P):
        W = np.zeros((P, P), dtype=np.int64)
        for i, ea in enumerate(Eset):
            coef = pow(u, ea, P)
            if coef:
                W += coef * gl[i]
        W %= P
        N += int(np.count_nonzero(W == 0))
    return N

def n_t_report(p, A, B, tval):
    monos = s4_monomials(p, A, B, tval)
    return n_t_bruteforce(p, monos, axis=0), len(monos)

# ---------------------------------------------------------------- cells
def cell_run(p, A, B, m, extra, K, seed0):
    """quo-vector + per-target (tval, V) so N_T can be normalized per target."""
    F = GF(p); Dmax = 2**(m - 1) + m * (m + extra) + 5
    out = []
    for k in range(K):
        dt = decomposable_target(F, A, B, m, extra=extra, seed=seed0 + k)
        if dt is None: continue
        tval, V = dt
        r = measure_system(F, A, B, m, tval, V, Dmax)
        if r['dim'] == 0 and r['quo'] is not None:
            out.append((int(r['quo']), int(tval), len(V)))
    return out

def match_nearest(order, curves, used):
    best = bd = None
    for i, c in enumerate(curves):
        if i in used: continue
        d = abs(c['order'] - order)
        if bd is None or d < bd: bd = d; best = i
    return best

def signflip_p(deltas, R=20000, seed=12345, two_sided=True):
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

def _f(x): return "None" if x is None else ("%+.4f" % x)

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

if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    print(">>> C1 firing plant (must show quo far above the ~1-6 baseline):")
    pl = plant_high_quo(541, 0, 7, 3, n_decomps=3, seed=5, maxV=7)
    print("    plant: quo=%s dim=%s made=%d sizeV=%d" % (pl['quo'], pl['dim'], pl['made'], pl['sizeV']))
    m = 3
    if SMOKE:
        pr = primes_1mod3(200, 2)
    else:
        pr = primes_1mod3(200, 12, cap=1000)

    # freeze schedule BEFORE first quo / first N_T
    sched = []
    for p in pr:
        cs = build_curves(p, 5, seed=1000 + p)
        sched.append(dict(p=p, curves=[{k: c[k] for k in ('lab', 'A', 'B', 'order', 'mu', 'kappa')} for c in cs]))
    blob = json.dumps(sched, sort_keys=True).encode()
    sha = hashlib.sha256(blob).hexdigest()
    open("_SCHEDULE_v5_B.json", "wb").write(blob)
    open("_SCHEDULE_v5_B.sha256", "w").write(sha + "\n")
    print("FROZEN Arm B schedule SHA-256 (before first quo):", sha)
    print("primes:", pr)

    extras = [1, 2, 3]  # |V| = 4,5,6
    Rp = 2000 if SMOKE else 20000
    nts_report = []   # (p, lab, order, N_T, #E^2) diagnostics

    for extra in extras:
        V = m + extra
        print("=" * 78)
        print("tag=ARMB-V=%d  m=%d K=10  #primes=%d" % (V, m, len(pr)))
        dE_j0 = []; dE_j17 = []; dj0 = []; dj17 = []
        for p in pr:
            t0 = time.time()
            cs = build_curves(p, 5, seed=1000 + p)
            for c in cs:
                cells = cell_run(p, c['A'], c['B'], m, extra, 10, seed0=7000)
                # per-target N_T (curve- and target-specific)
                Es = []
                for (q, tval, kV) in cells:
                    NT, nmono = n_t_report(p, c['A'], c['B'], tval)
                    if NT > 0:
                        Es.append(math.log(q * float(p)**3 / (kV**3 * NT)))
                    nts_report.append((p, c['lab'], c['order'], NT, c['order']**2))
                c['E'] = Es
                c['Q'] = [math.log(x[0]) for x in cells] if cells else None
                c['cells'] = cells
            noncm = [c for c in cs if c['lab'] == 'nonCM']
            cj0 = [c for c in cs if c['lab'] == 'j0'][0]
            cj17 = [c for c in cs if c['lab'] == 'j1728'][0]
            used = set()
            i0 = match_nearest(cj0['order'], noncm, used); used.add(i0)
            i17 = match_nearest(cj17['order'], noncm, used); used.add(i17)
            if cj0['E'] and noncm[i0]['E']:
                dE_j0.append(sum(cj0['E']) / len(cj0['E']) - sum(noncm[i0]['E']) / len(noncm[i0]['E']))
            if cj17['E'] and noncm[i17]['E']:
                dE_j17.append(sum(cj17['E']) / len(cj17['E']) - sum(noncm[i17]['E']) / len(noncm[i17]['E']))
            if cj0['Q'] and noncm[i0]['Q']:
                dj0.append(sum(cj0['Q']) / len(cj0['Q']) - sum(noncm[i0]['Q']) / len(noncm[i0]['Q']))
            if cj17['Q'] and noncm[i17]['Q']:
                dj17.append(sum(cj17['Q']) / len(cj17['Q']) - sum(noncm[i17]['Q']) / len(noncm[i17]['Q']))
            print("  p=%-5d T1j0=%s T1j17=%s Texcess_j0=%s Texcess_j17=%s [%.0fs]"
                  % (p, _f(dj0[-1] if dj0 else None), _f(dj17[-1] if dj17 else None),
                     _f(dE_j0[-1] if dE_j0 else None), _f(dE_j17[-1] if dE_j17 else None),
                     time.time() - t0))
        print("-" * 50)
        for nm, xs in [("T1_excess(j0)   ", dE_j0), ("T1_excess(j1728)", dE_j17),
                       ("T1(j0)          ", dj0), ("T1(j1728)       ", dj17)]:
            obs, pv = signflip_p(xs, R=Rp, two_sided=(nm.startswith("T1_excess")))
            n = len(xs) if xs else 0
            pos = 0
            if xs:
                for x in xs:
                    if x > 0: pos += 1
            print("  %-16s n=%-2d mean=%s  perm_p=%s  (pos %d/%d)" % (nm, n, _f(obs), _f(pv), pos, n))

    # N_T diagnostics: N_T vs #E^2
    print("\nN_T vs #E^2 diagnostics (surface count vs group-count model):")
    for (p, lab, order, NT, E2) in nts_report[:12]:
        print("  p=%-4d %-6s #E=%-5d N_T=%-8d #E^2=%-9d N_T/#E^2=%.4f"
              % (p, lab, order, NT, E2, NT / float(E2)))
    if nts_report:
        cm_ratio = [NT / float(E2) for (p, l, o, NT, E2) in nts_report if l == 'j0']
        nc_ratio = [NT / float(E2) for (p, l, o, NT, E2) in nts_report if l == 'nonCM']
        if cm_ratio and nc_ratio:
            print("  mean N_T/#E^2: j0=%.4f  nonCM=%.4f" %
                  (sum(cm_ratio) / len(cm_ratio), sum(nc_ratio) / len(nc_ratio)))

    # C7: recompute one target axis-flipped (p = pr[0], j0 curve, its first logged target)
    print("\nC7 N_T cross-validation (axis-flipped recomputation):")
    p0 = pr[0]
    cs0 = build_curves(p0, 5, seed=1000 + p0)
    done = 0
    for c in cs0:
        if done >= 3: break
        cells = cell_run(p0, c['A'], c['B'], m, 1, 2, seed0=7000)  # |V|=4, K=2
        for (q, tval, kV) in cells[:1]:
            monos = s4_monomials(p0, c['A'], c['B'], tval)
            n_ax0 = n_t_bruteforce(p0, monos, axis=0)
            n_ax2 = n_t_bruteforce(p0, monos, axis=2)
            ok = (n_ax0 == n_ax2)
            print("  p=%d %s t=%d: N_T(axis0)=%d N_T(axis2)=%d  [%s]"
                  % (p0, c['lab'], tval, n_ax0, n_ax2, "EXACT MATCH" if ok else "*** MISMATCH ***"))
            done += 1
            break

    print("\n[PROVISIONAL — experiment-designer gate on PREREG v5 OWED before grading]")
