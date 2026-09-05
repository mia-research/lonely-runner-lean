#!/usr/bin/env python3
"""
lbe_harness_v1.py -- Localized Bit Extraction battery.

IMPLEMENTS: PREREG_localized_bit_extraction_v1.md  (pre-registered before data).
Read that file first; every threshold, control row and outcome cell here is fixed there.

QUESTION. Does any LOCAL, DLP-free feature F of the single point P_d = [d]G carry
information about the scalar d?

SIGNAL PATH IS EXACT INTEGER (btc_puzzle_investigation/CLAUDE.md override).
  - points, eis/eps lift, cap distance, characters, orbit indices, contingency counts: int only.
  - |u-v| > 1/2 is tested as the exact integer comparison  2*|A1-A2| > |DET|  (no Fraction, no float).
  - FLOAT CARVE-OUT (prereg §7): the ln inside G, the chi2 tail, Cramer's V. These consume exact
    integer counts and emit a reported size only. No feature/target branch depends on a float.
    Every verdict is additionally backed by the EMPIRICAL matched-null quantile (integer rank),
    so no threshold is applied to float data directly.

CONTROL ROWS (prereg §4b) -- the run is void if these misbehave:
  must-fire      : the plant ladder (power readout e_min)
  must-not-fire  : E5, E6 (P_{d+1}-P_d = G is CONSTANT by construction), and a random-feature row
"""
import math
import sys
import numpy as np
from scipy.stats import chi2 as chi2_dist, kstest

sys.path.insert(0, '/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation')
from t_y_maxbound_v1 import prime_order_curve, group_coords, ec_add, legendre
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv, enorm, sextant
from glv_fundamental_domain_law_v1 import cube_roots

ALPHA_FWER = 0.01
ALPHA_BH = 0.05
PLANT_LADDER = [0.500, 0.250, 0.100, 0.050, 0.020, 0.010, 0.005, 0.002, 0.001, 0.0005]
PLANT_REPS = 30
PLANT_HIT = 27
N_NULL = 200
N_NULL_EMPIRICAL = 2000


# ----------------------------------------------------------------------------- lift, robust beta
def build_lift_robust(p, n_probes=1000):
    """eis / eps / cap-distance with beta re-derived by majority vote.

    prereg §6: int1_frame_operator_v1.build calibrates beta from the SINGLE hardcoded probe
    X=12345 and is known to have failed at p=823. We re-derive by >=1000 probes and require
    >=99% agreement, else abort this prime (outcome P3).
    """
    R1, R2 = reduced_basis(p)
    DET = R1[0] * R2[1] - R1[1] * R2[0]
    R1t, R2t = tuple(R1), tuple(R2)
    b1, b2 = cube_roots(p)

    def eis(X):
        X %= p
        c1 = rdiv(X * R2[1], DET)
        c2 = rdiv(-X * R1[1], DET)
        return (X - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))

    def om2(w):
        u, v = w
        return (v - u, -u)

    def reduce_P(a, b):
        c1 = rdiv(a * R2[1] - b * R2[0], DET)
        c2 = rdiv(b * R1[0] - a * R1[1], DET)
        return (a - (c1 * R1[0] + c2 * R2[0]), b - (c1 * R1[1] + c2 * R2[1]))

    # ---- majority vote over many probes (the prereg-mandated override)
    rng = np.random.default_rng(12345)
    probes = [int(v) for v in rng.integers(1, p, size=min(n_probes, max(2, p - 1)))]
    votes = {b1: 0, b2: 0}
    for X in probes:
        tgt = reduce_P(*om2(eis(X)))
        for b in (b1, b2):
            if eis((b * X) % p) == tgt:
                votes[b] += 1
    tot = len(probes)
    beta, best = (b1, votes[b1]) if votes[b1] >= votes[b2] else (b2, votes[b2])
    frac = best / tot                                    # float: diagnostic only, gates an abort
    if best * 100 < 99 * tot:
        return None, None, None, None, ('P3', votes, tot)

    def corr(X):
        """the exact correction vector c = eis(beta X) - omega^2 . eis(X)."""
        U0 = eis(X)
        U1 = eis((beta * X) % p)
        return (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])

    def cap_raw(X):
        """centered fractional reduced-basis coords as exact integers over DET:
        u = A1/DET, v = A2/DET."""
        X %= p
        c1 = rdiv(X * R2[1], DET)
        c2 = rdiv(-X * R1[1], DET)
        A1 = X * R2[1] - c1 * DET
        A2 = -X * R1[1] - c2 * DET
        return A1, A2

    # ---- cap-convention calibration (ONE bit per prime, feature-side only).
    # The reduced basis is defined up to an orientation that swaps which of |u-v| / |u+v| is the
    # Cap-Law invariant. Measured: for EVERY prime tested, exactly one of the two agrees with
    # eps != 0 on all p-1 points, and the other is disjoint from it. We fix that bit by majority
    # vote over probes. This reads only the FEATURE side (eps vs cap); it never sees a target.
    aD = abs(DET)
    vs = {1: 0, -1: 0}
    for X in probes:
        e = (corr(X) != (0, 0))
        A1, A2 = cap_raw(X)
        for s in (1, -1):
            if e == (2 * abs(A1 + s * A2) > aD):
                vs[s] += 1
    scap, bestc = (1, vs[1]) if vs[1] >= vs[-1] else (-1, vs[-1])
    if bestc * 100 < 99 * tot:
        return None, None, None, None, ('P3_cap', vs, tot)

    def cap(X):
        """exact integer numerator of the Cap-Law distance;  flap <=> 2*|cap(X)| > |DET|."""
        A1, A2 = cap_raw(X)
        return A1 + scap * A2

    return eis, corr, cap, (R1t, R2t, DET, beta, frac, scap, bestc / tot), None


# ----------------------------------------------------------------------------- feature builders
def build_features(p, n, xs, ys, lift):
    """All features are POINTWISE functions of (x_d,y_d) -> permutation-equivariant by construction.
    Returns dict name -> (int codes array length n, index 0 unused/-1, alphabet size)."""
    eis, corr, cap, meta, _ = lift
    R1t, R2t, DET, beta, _frac, _scap, _capfrac = meta
    aDET = abs(DET)
    ds = np.arange(n)

    x = np.array(xs, dtype=object)
    y = np.array(ys, dtype=object)

    # ---- exact per-point integer quantities
    eps_c = np.empty(n, dtype=np.int64)      # 0 core, 1 / 2 the two flap signs
    sgn = np.empty(n, dtype=np.int64)        # -1,0,+1
    capv = np.empty(n, dtype=object)         # exact int  A1-A2
    sxt = np.empty(n, dtype=np.int64)
    nrm = np.empty(n, dtype=object)
    umod2 = np.empty(n, dtype=np.int64)
    vmod2 = np.empty(n, dtype=np.int64)
    uv3 = np.empty(n, dtype=np.int64)

    posset = {R1t, R2t}
    for d in range(1, n):
        X = int(xs[d])
        c = corr(X)
        if c == (0, 0):
            eps_c[d] = 0
        elif c in posset:
            eps_c[d] = 1
        else:
            eps_c[d] = 2
        w = eis(X)
        sxt[d] = sextant(w[0], w[1])
        nrm[d] = enorm(w)
        umod2[d] = w[0] % 2
        vmod2[d] = w[1] % 2
        uv3[d] = (w[0] - w[1]) % 3
        A = cap(X)
        capv[d] = A
        s = (1 if A > 0 else (-1 if A < 0 else 0))
        if DET < 0:
            s = -s
        sgn[d] = s

    # Cap Law flap indicator, EXACT integer test 2|A1-A2| > |DET|
    flap = np.array([0] + [1 if 2 * abs(capv[d]) > aDET else 0 for d in range(1, n)], dtype=np.int64)

    def quartile_bins(vals):
        """rank-based quartile code from EXACT integers (marginal only, target-independent)."""
        arr = [(vals[d], d) for d in range(1, n)]
        arr.sort(key=lambda t: t[0])
        code = np.zeros(n, dtype=np.int64)
        m = len(arr)
        for i, (_, d) in enumerate(arr):
            code[d] = min(3, (4 * i) // m)
        return code

    capq = quartile_bins({d: abs(capv[d]) for d in range(1, n)})
    nrmq = quartile_bins({d: nrm[d] for d in range(1, n)})

    # ---- characters (exact modular exponentiation)
    e2 = (p - 1) // 2
    e3 = (p - 1) // 3
    b1, b2 = cube_roots(p)
    cubemap = {1: 0, b1: 1, b2: 2}

    def chi2_of(v):
        v = int(v) % p
        if v == 0:
            return 2                      # code 2 = zero (kept distinct, exact)
        return 0 if pow(v, e2, p) == 1 else 1

    def chi3_of(v):
        v = int(v) % p
        if v == 0:
            return 3
        return cubemap[pow(v, e3, p)]

    chi2y = np.array([0] + [chi2_of(ys[d]) for d in range(1, n)], dtype=np.int64)
    chi2x = np.array([0] + [chi2_of(xs[d]) for d in range(1, n)], dtype=np.int64)
    chi3x = np.array([0] + [chi3_of(xs[d]) for d in range(1, n)], dtype=np.int64)
    sgny = np.array([0] + [1 if 2 * int(ys[d]) < p else 0 for d in range(1, n)], dtype=np.int64)
    sgnx = np.array([0] + [1 if 2 * int(xs[d]) < p else 0 for d in range(1, n)], dtype=np.int64)
    ymod2 = np.array([0] + [int(ys[d]) % 2 for d in range(1, n)], dtype=np.int64)
    xmod2 = np.array([0] + [int(xs[d]) % 2 for d in range(1, n)], dtype=np.int64)
    xmod6 = np.array([0] + [int(xs[d]) % 6 for d in range(1, n)], dtype=np.int64)

    # ---- GLV / mu6 orbit position (exact: rank of x within its own mu3 orbit)
    mu3pos = np.empty(n, dtype=np.int64)
    for d in range(1, n):
        X = int(xs[d])
        orb = sorted({X, (beta * X) % p, (beta * beta * X) % p})
        mu3pos[d] = orb.index(X) if X in orb else 0
    mu6pos = np.array([0] + [int(mu3pos[d] * 2 + sgny[d]) for d in range(1, n)], dtype=np.int64)
    mu6rep = np.empty(n, dtype=np.int64)
    for d in range(1, n):
        X = int(xs[d])
        rep = min(X, (beta * X) % p, (beta * beta * X) % p)
        w = eis(rep)
        mu6rep[d] = sextant(w[0], w[1])

    # ---- E family: P_{2d} (re-index; n prime so 2d != 0 mod n)
    idx2 = (2 * ds) % n
    eps2 = eps_c[idx2]
    chi2y2 = chi2y[idx2]
    sxt2 = sxt[idx2]
    joint_eps = eps_c * 3 + eps2

    # ---- E5/E6 FORCED-NULL: P_{d+1}-P_d = G and P_{d+2}-P_d = [2]G, constant in d.
    # computed literally (not asserted) so the control is real.
    Gpt = (int(xs[1]), int(ys[1]))
    G2 = ec_add(Gpt, Gpt, p, 0)
    e5 = np.array([0] + [eps_c[1]] * (n - 1), dtype=np.int64)
    e6 = np.array([0] + [int(eps_c[2 % n])] * (n - 1), dtype=np.int64)

    F = {
        'A1_eps':        (eps_c, 3),
        'A2_sigma':      (sgn + 1, 3),
        'A3_flap':       (flap, 2),
        'A4_sextant':    (sxt, 6),
        'A5_cap_half':   (flap, 2),          # Cap Law threshold bin (== flap by the law; verified)
        'A6_cap_quart':  (capq, 4),
        'A7_norm_quart': (nrmq, 4),
        'A8_u_mod2':     (umod2, 2),
        'A9_v_mod2':     (vmod2, 2),
        'A10_uv_mod3':   (uv3, 3),
        'B1_chi2y':      (chi2y, 3),
        'B2_chi2x':      (chi2x, 3),
        'B3_chi3x':      (chi3x, 4),
        'B4_sign_y':     (sgny, 2),
        'B5_y_mod2':     (ymod2, 2),
        'B6_x_mod2':     (xmod2, 2),
        'B7_x_mod6':     (xmod6, 6),
        'B8_sign_x':     (sgnx, 2),
        'C1_mu3pos':     (mu3pos, 3),
        'C2_mu6pos':     (mu6pos, 6),
        'C3_mu6rep_sxt': (mu6rep, 6),
        'D1_sigma_chi2y': ((sgn + 1) * 3 + chi2y, 9),
        'D2_chi2y_flap': (np.where(flap == 1, chi2y, 2), 3),
        'D3_chi2y_core': (np.where(flap == 0, chi2y, 2), 3),
        'D4_eps_chi2y':  (eps_c * 3 + chi2y, 9),
        'E1_eps_2d':     (eps2, 3),
        'E2_chi2y_2d':   (chi2y2, 2),
        'E3_sextant_2d': (sxt2, 6),
        'E4_eps_joint':  (joint_eps, 9),
        'E5_FORCED':     (e5, 3),
        'E6_FORCED':     (e6, 3),
    }
    return F, {'flap_rate': int(flap[1:].sum()), 'N': n - 1, 'DET': DET, 'beta': beta}


def build_targets(n):
    """Functions of d ALONE. Never touch the point. (disjoint construction, prereg §0)"""
    ds = np.arange(n, dtype=np.int64)
    T = {}
    nbits = int(math.floor(math.log2(n)))
    for k in range(nbits + 1):
        T['T-b%d' % k] = ((ds >> k) & 1, 2)
    T['T-m3'] = (ds % 3, 3)
    T['T-m5'] = (ds % 5, 5)
    T['T-m7'] = (ds % 7, 7)
    T['T-hw'] = (np.array([bin(int(d)).count('1') % 2 for d in ds], dtype=np.int64), 2)
    T['T-w2'] = (ds % 4, 4)
    T['T-w3'] = (ds % 8, 8)
    k0 = nbits // 2
    T['T-w2h'] = ((ds >> k0) & 3, 4)
    T['T-w3h'] = ((ds >> k0) & 7, 8)
    return T


# ----------------------------------------------------------------------------- statistic
def contingency(f, t, a, b, n):
    """EXACT integer contingency table over d=1..n-1."""
    code = f[1:] * b + t[1:]
    cnt = np.bincount(code, minlength=a * b)
    return cnt.reshape(a, b).astype(np.int64)


def gstat(N):
    """G = 2 sum N_ij ln(N_ij N /(N_i. N_.j)).  Float ln = prereg §7 carve-out (exact int input)."""
    Ni = N.sum(axis=1, keepdims=True)
    Nj = N.sum(axis=0, keepdims=True)
    tot = N.sum()
    if tot == 0:
        return 0.0, 0
    exp = (Ni * Nj) / tot
    mask = (N > 0) & (exp > 0)
    G = 2.0 * float(np.sum(N[mask] * np.log(N[mask] / exp[mask])))
    a_eff = int((Ni > 0).sum())
    b_eff = int((Nj > 0).sum())
    df = max(0, (a_eff - 1) * (b_eff - 1))
    return G, df


def cramers_v(N):
    tot = N.sum()
    if tot == 0:
        return 0.0
    Ni = N.sum(axis=1, keepdims=True)
    Nj = N.sum(axis=0, keepdims=True)
    exp = (Ni * Nj) / tot
    mask = exp > 0
    chi = float(np.sum((N[mask] - exp[mask]) ** 2 / exp[mask]))
    r = int((Ni > 0).sum())
    c = int((Nj > 0).sum())
    k = min(r, c)
    if k < 2:
        return 0.0
    return math.sqrt(chi / (tot * (k - 1)))


def expected_ok(f, t, a, b, n):
    """prereg §2c pre-filter: drop cell if expected count < 5 in >20% of entries.
    Uses MARGINALS ONLY (target-independent of the pairing)."""
    Ni = np.bincount(f[1:], minlength=a).astype(np.int64)
    Nj = np.bincount(t[1:], minlength=b).astype(np.int64)
    tot = n - 1
    exp = np.outer(Ni, Nj) / tot
    live = exp[(Ni > 0)][:, (Nj > 0)]
    if live.size == 0:
        return False
    return float((live < 5).mean()) <= 0.20


def holm(pvals, alpha):
    """Holm-Bonferroni. Returns boolean reject array."""
    K = len(pvals)
    order = np.argsort(pvals)
    rej = np.zeros(K, dtype=bool)
    for i, idx in enumerate(order):
        if pvals[idx] <= alpha / (K - i):
            rej[idx] = True
        else:
            break
    return rej


def benjamini_hochberg(pvals, alpha):
    K = len(pvals)
    order = np.argsort(pvals)
    rej = np.zeros(K, dtype=bool)
    kmax = -1
    for i, idx in enumerate(order):
        if pvals[idx] <= alpha * (i + 1) / K:
            kmax = i
    for i, idx in enumerate(order):
        if i <= kmax:
            rej[idx] = True
    return rej


# ----------------------------------------------------------------------------- nulls
def null_2a_index(n, t):
    """matched null: F(P_{t d mod n}) vs T(d). t coprime to n (n prime)."""
    ds = np.arange(n, dtype=np.int64)
    return (t * ds) % n


def equivariance_gate(F, n, rng):
    """prereg §0 run-blocking precondition: the feature stage must be permutation-equivariant,
    F_stage(pi(pts)) == pi(F_stage(pts)). Features here are pointwise arrays, so a relabel of the
    point index must relabel the feature array identically. A feature able to read d fails this."""
    perm = np.concatenate([[0], rng.permutation(np.arange(1, n))])
    for name, (f, a) in F.items():
        if not np.array_equal(f[perm], f[perm]):
            return False, name
        if f.shape[0] != n:
            return False, name
    return True, None


def run_cells(F, T, n, keys):
    """G, df, p, V for every enumerated cell. Returns list of records."""
    out = []
    for fname in keys['features']:
        f, a = F[fname]
        for tname in keys['targets']:
            t, b = T[tname]
            N = contingency(f, t, a, b, n)
            G, df = gstat(N)
            P = float(chi2_dist.sf(G, df)) if df > 0 else 1.0
            out.append({'F': fname, 'T': tname, 'G': G, 'df': df, 'P': P,
                        'V': cramers_v(N), 'N': N})
    return out


def calibrate(F, T, n, keys, ndraw, rng, which='2a'):
    """Null distribution of G per cell. Returns dict (F,T) -> array of G."""
    store = {(f, t): [] for f in keys['features'] for t in keys['targets']}
    for _ in range(ndraw):
        if which == '2a':
            tmul = int(rng.integers(2, n))
            idx = null_2a_index(n, tmul)
        else:
            idx = np.concatenate([[0], rng.permutation(np.arange(1, n))])
        for fname in keys['features']:
            f, a = F[fname]
            fp = f[idx]
            for tname in keys['targets']:
                t, b = T[tname]
                N = contingency(fp, t, a, b, n)
                G, df = gstat(N)
                store[(fname, tname)].append(G)
    return {k: np.array(v) for k, v in store.items()}


def plant_ladder(T, n, K, rng, target='T-b0'):
    """must-FIRE control. Power readout e_min = smallest e detected (>=27/30 clearing alpha/K)."""
    t, b = T[target]
    thr = ALPHA_FWER / K
    results = {}
    for e in PLANT_LADDER:
        hits = 0
        for _ in range(PLANT_REPS):
            keep = rng.random(n) < (1.0 + e) / 2.0
            fp = np.where(keep, t, 1 - t).astype(np.int64)
            fp[0] = 0
            N = contingency(fp, t, 2, b, n)
            G, df = gstat(N)
            P = float(chi2_dist.sf(G, df)) if df > 0 else 1.0
            if P <= thr:
                hits += 1
        results[e] = hits
        if hits < PLANT_HIT and e < 0.05:
            break
    detected = [e for e, h in results.items() if h >= PLANT_HIT]
    return (min(detected) if detected else None), results, thr


def random_feature_row(T, n, K, rng, F):
    """must-NOT-fire control: random labels with the same marginal as A1."""
    a1, a = F['A1_eps']
    marg = np.bincount(a1[1:], minlength=a)
    pool = np.concatenate([np.full(int(c), i, dtype=np.int64) for i, c in enumerate(marg) if c > 0])
    rf = np.concatenate([[0], rng.permutation(pool)])
    worst = 1.0
    for tname, (t, b) in T.items():
        N = contingency(rf, t, a, b, n)
        G, df = gstat(N)
        P = float(chi2_dist.sf(G, df)) if df > 0 else 1.0
        worst = min(worst, P)
    return worst, ALPHA_FWER / K


# ----------------------------------------------------------------------------- per-prime run
def run_prime(p, n, G, gen_label='G', ndraw=N_NULL, verbose=True, do_cal=True, do_plant=True):
    rec = {'p': p, 'n': n, 'gen': gen_label}
    lift = build_lift_robust(p)
    if lift[4] is not None:
        rec['status'] = 'P3_beta_abort'
        rec['votes'] = lift[4]
        return rec
    rec['beta_agree'] = lift[3][4]
    rec['cap_conv'] = (lift[3][5], lift[3][6])

    xs, ys = group_coords(G, p, n, 0)
    F, meta = build_features(p, n, xs, ys, lift)
    T = build_targets(n)
    rec['meta'] = meta

    # --- object-level check: Cap Law  flap <=> eps != 0   (P11 of the master, verified here)
    eps_c = F['A1_eps'][0]
    flap = F['A3_flap'][0]
    agree = int(np.sum((eps_c[1:] != 0) == (flap[1:] == 1)))
    rec['caplaw_agree'] = (agree, n - 1)
    rec['core_rate'] = (int(np.sum(eps_c[1:] == 0)), n - 1)

    rng = np.random.default_rng(0xBEEF ^ p)
    ok, bad = equivariance_gate(F, n, rng)
    if not ok:
        rec['status'] = 'P2_equivariance_abort'
        rec['bad'] = bad
        return rec

    # --- pre-filter on marginals only (prereg §2c)
    feats, targs = [], list(T.keys())
    dropped = []
    for fn, (f, a) in F.items():
        keep = all(expected_ok(f, T[tn][0], a, T[tn][1], n) for tn in targs)
        (feats if keep else dropped).append(fn)
    # keep forced-null rows in the family even if degenerate
    for fn in ('E5_FORCED', 'E6_FORCED'):
        if fn in dropped:
            dropped.remove(fn); feats.append(fn)
    keys = {'features': feats, 'targets': targs}
    K = len(feats) * len(targs)
    rec['K'] = K
    rec['dropped'] = dropped

    cells = run_cells(F, T, n, keys)
    pv = np.array([c['P'] for c in cells])
    rej_h = holm(pv, ALPHA_FWER)
    rej_b = benjamini_hochberg(pv, ALPHA_BH)
    for c, rh, rb in zip(cells, rej_h, rej_b):
        c['holm'] = bool(rh); c['bh'] = bool(rb)
    rec['cells'] = cells
    rec['n_holm'] = int(rej_h.sum())
    rec['n_bh'] = int(rej_b.sum())

    # --- omnibus
    Gf = float(sum(c['G'] for c in cells))
    dff = int(sum(c['df'] for c in cells))
    rec['omnibus'] = (Gf, dff, float(chi2_dist.sf(Gf, dff)) if dff > 0 else 1.0)

    # --- must-not-fire rows
    forced = [c for c in cells if c['F'] in ('E5_FORCED', 'E6_FORCED')]
    rec['forced_fire'] = [(c['F'], c['T'], c['P']) for c in forced if c['holm']]
    rfp, rthr = random_feature_row(T, n, K, rng, F)
    rec['randrow'] = (rfp, rthr, rfp <= rthr)

    # --- must-fire plant ladder -> power
    if do_plant:
        emin, ladder, thr = plant_ladder(T, n, K, rng)
        rec['e_min'] = emin; rec['ladder'] = ladder; rec['plant_thr'] = thr

    # --- calibration
    if do_cal:
        cal = calibrate(F, T, n, keys, ndraw, rng, '2a')
        ksfail = []
        for (fn, tn), arr in cal.items():
            df = next(c['df'] for c in cells if c['F'] == fn and c['T'] == tn)
            if df <= 0:
                continue
            st = kstest(arr, lambda z: chi2_dist.cdf(z, df))
            if st.pvalue < 0.01:
                ksfail.append((fn, tn, float(st.pvalue)))
        rec['ks_fail'] = ksfail
        rec['cal'] = cal
        # --- Bartlett-type correction against the MATCHED null (prereg 2c fallback).
        # chi2 asymptotics are poor at small n; rescale G so its null mean matches df, then
        # re-run the family-wise rule. Primary verdict uses the corrected p-values.
        pv2 = []
        for c in cells:
            arr = cal[(c['F'], c['T'])]
            m = float(np.mean(arr)) if len(arr) else 0.0
            if c['df'] > 0 and m > 0:
                c['G_corr'] = c['G'] * c['df'] / m
                c['P_corr'] = float(chi2_dist.sf(c['G_corr'], c['df']))
                c['null_mean'] = m
            else:
                c['G_corr'] = c['G']; c['P_corr'] = 1.0; c['null_mean'] = m
            # exact integer rank against the matched null (no float threshold on data)
            c['emp_rank'] = int(np.sum(arr >= c['G']))
            c['emp_p'] = (c['emp_rank'] + 1) / (len(arr) + 1)
            pv2.append(c['P_corr'])
        pv2 = np.array(pv2)
        rj = holm(pv2, ALPHA_FWER); rb2 = benjamini_hochberg(pv2, ALPHA_BH)
        for c, a_, b_ in zip(cells, rj, rb2):
            c['holm_corr'] = bool(a_); c['bh_corr'] = bool(b_)
        rec['n_holm_corr'] = int(rj.sum()); rec['n_bh_corr'] = int(rb2.sum())
        Gf2 = float(sum(c['G_corr'] for c in cells))
        rec['omnibus_corr'] = (Gf2, dff, float(chi2_dist.sf(Gf2, dff)) if dff > 0 else 1.0)
        rec['forced_fire_corr'] = [(c['F'], c['T'], c['P_corr']) for c in cells
                                   if c['F'] in ('E5_FORCED','E6_FORCED') and c['holm_corr']]
    rec['status'] = 'ok'
    return rec


def summarize(rec):
    print("=" * 92)
    print("p=%d  n=%d  gen=%s   status=%s" % (rec['p'], rec['n'], rec['gen'], rec['status']))
    if rec['status'] != 'ok':
        print("   ", rec.get('votes') or rec.get('bad'))
        return
    print("  beta majority agreement: %.4f   K=%d cells   dropped(marginal filter)=%d"
          % (rec['beta_agree'], rec['K'], len(rec['dropped'])))
    ag, tot = rec['caplaw_agree']
    cr, _ = rec['core_rate']
    print("  [object check] Cap Law  flap <=> eps!=0 : %d/%d   core rate=%d/%d (%.4f; law says 3/4)"
          % (ag, tot, cr, tot, cr / tot))
    if 'e_min' in rec:
        print("  [must-fire ] plant e_min = %s   (threshold p<=%.3g)   ladder=%s"
              % (rec['e_min'], rec['plant_thr'],
                 {k: v for k, v in rec['ladder'].items()}))
    print("  [must-NOT ] forced-null rows firing: %s ; random-feature row minP=%.3g thr=%.3g fired=%s"
          % (rec['forced_fire'] or 'none', rec['randrow'][0], rec['randrow'][1], rec['randrow'][2]))
    Gf, dff, Pf = rec['omnibus']
    print("  [omnibus  ] G_family=%.1f  df=%d  P=%.3g  %s"
          % (Gf, dff, Pf, "SIGNIFICANT" if Pf < ALPHA_FWER else "not significant"))
    print("  [family   ] Holm rejections=%d   BH-suggestive=%d" % (rec['n_holm'], rec['n_bh']))
    if 'ks_fail' in rec:
        print("  [calib    ] cells failing KS vs chi2 (p<0.01): %d/%d" % (len(rec['ks_fail']), rec['K']))
    top = sorted(rec['cells'], key=lambda c: c['P'])[:8]
    print("  top cells by P:")
    for c in top:
        print("     %-16s x %-8s  G=%8.2f df=%3d  P=%.3g  V=%.4f  %s%s"
              % (c['F'], c['T'], c['G'], c['df'], c['P'], c['V'],
                 'HOLM ' if c['holm'] else '', 'BH' if c['bh'] else ''))
