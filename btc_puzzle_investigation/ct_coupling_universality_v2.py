#!/usr/bin/env python3
"""
C_T inter-coordinate coupling: UNIVERSAL constant, or NOISE FLOOR?  (implements
PREREG_ct_coupling_universality_v1.md; supersedes ct_coupling_universality_v1.py whose
max|Tj-Tf| stat + "constant-dev => universal coupling" logic DRILL 01 showed to be the floor.)

Primary statistic = surrogate-normalized pooled G^2 (z_G2), DECIDED BY ITS n-SCALING, not by
raw magnitude (a floor is flat / eps_hat ~ n^-0.5; a real coupling rises / eps_hat ~ n^0).
Headline magnitude = bias-corrected implied coupling eps_hat = sqrt(max(0,G2_real-mean G2_surr)/n).
Corroborators = swap-parity Frobenius channels ||D_odd||, ||D_even|| (surrogate-normalized).
Planted control (known coupling) GATES informativeness: if it does not fire at the power-table n,
the null is uninformative -- FULL STOP, no branch conclusion.

Exact integer state path (rdiv/reduced_basis; int64 count accumulators). Float only in
eig/ln/Frobenius/z -- analytic sizes / a monotone stat ranked vs the matched null (prereg S8).
Seed 20260719.  b=7 only, p<=2^17.  Branches A/B/C/D + subspace + FULL-STOP per prereg S7/S9.
"""
import numpy as np
from sympy import isprime, nextprime
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv

S9 = [(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1)]
I9 = {s: i for i, s in enumerate(S9)}
I3 = {-1: 0, 0: 1, 1: 2}
C3 = [-1, 0, 1]
SW = np.zeros((9, 9))
for i, (a, b) in enumerate(S9):
    SW[i, I9[(b, a)]] = 1.0
SEED = 20260719
MSUR = 40                       # surrogate draws per cell (pre-committed)

# ----------------------------------------------------------------------------- curve / lift
def curve_order(p):
    c = 1
    for x in range(p):
        r = (x * x * x + 7) % p
        if r == 0: c += 1
        elif pow(r, (p - 1) // 2, p) == 1: c += 2
    return c

def lift_funcs(p):
    R1, R2 = reduced_basis(p)
    DET = R1[0] * R2[1] - R1[1] * R2[0]
    def add_c(A, B):
        if A is None: return B
        if B is None: return A
        x1, y1 = A; x2, y2 = B
        if x1 == x2:
            if (y1 + y2) % p == 0: return None
            lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
        else:
            lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
        x3 = (lam * lam - x1 - x2) % p
        return (x3, (lam * (x1 - x3) - y1) % p)
    def eis(X):
        c1 = rdiv(X * R2[1], DET); c2 = rdiv(-X * R1[1], DET)
        return (X - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))
    def state(z1, z2):
        sx, sy = z1[0] + z2[0], z1[1] + z2[1]
        return (rdiv(sx * R2[1] - sy * R2[0], DET), rdiv(-sx * R1[1] + sy * R1[0], DET))
    return add_c, eis, state

def orbit_xlifts(p):
    """full-orbit x-coordinate lifts zx[1..n] for the first generator found."""
    add_c, eis, state = lift_funcs(p)
    G = None
    for x in range(1, p):
        r = (x * x * x + 7) % p
        if pow(r, (p - 1) // 2, p) == 1:
            y = sqrt_mod(r, p)
            if y: G = (x, int(y)); break
    pts = [None, G]; cur = G
    while True:
        cur = add_c(cur, G)
        if cur is None: break
        pts.append(cur)
    n = len(pts) - 1
    zx = [None] + [eis(pts[k][0]) for k in range(1, n + 1)]
    return zx, n, state

def states_step(zx, n, state, h, start, count):
    """the addition-rounding state along the step-h walk, `count` states from `start`."""
    seq = []
    j = start % n
    if j == 0: j = n
    idx = [j]
    for _ in range(count):          # count+1 points -> count states
        j = j + h
        while j > n: j -= n
        idx.append(j)
    for t in range(len(idx) - 1):
        seq.append(state(zx[idx[t]], zx[idx[t + 1]]))
    return seq

# ----------------------------------------------------------------------------- estimators
def count_tables(seq):
    """integer transition counts: Cj 9x9 (source->target), plus coord marginals C1,C2 3x3."""
    Cj = np.zeros((9, 9), dtype=np.int64)
    C1 = np.zeros((3, 3), dtype=np.int64)
    C2 = np.zeros((3, 3), dtype=np.int64)
    for a, b in zip(seq[:-1], seq[1:]):
        if a in I9 and b in I9:
            Cj[I9[a], I9[b]] += 1
            C1[I3[a[0]], I3[b[0]]] += 1
            C2[I3[a[1]], I3[b[1]]] += 1
    return Cj, C1, C2

def norm_rows(C):
    C = C.astype(float); rs = C.sum(1, keepdims=True); rs[rs == 0] = 1.0
    return C / rs

def tensor(T1, T2):
    Tf = np.zeros((9, 9))
    for si, (i, j) in enumerate(S9):
        for sk, (k, l) in enumerate(S9):
            Tf[si, sk] = T1[I3[i], I3[k]] * T2[I3[j], I3[l]]
    return Tf

def g2_pooled(Cj):
    """pooled likelihood-ratio G^2 for 'next coords independent within each source state'.
    Cj[s,:] is a 9-vector of counts of next-state (c1',c2') from source s; reshape 3x3, test
    row/col independence; sum G^2 over the 9 source states. Exact-int counts; ln = analytic."""
    G2 = 0.0
    for s in range(9):
        N = Cj[s].reshape(3, 3).astype(float)
        tot = N.sum()
        if tot < 1: continue
        rm = N.sum(1, keepdims=True); cm = N.sum(0, keepdims=True)
        E = rm @ cm / tot
        mask = (N > 0) & (E > 0)
        G2 += 2.0 * np.sum(N[mask] * np.log(N[mask] / E[mask]))
    return G2

def swap_channels(Tj, Tf):
    D = Tj - Tf
    Dsw = SW @ D @ SW
    Deven = 0.5 * (D + Dsw); Dodd = 0.5 * (D - Dsw)
    return float(np.linalg.norm(Deven)), float(np.linalg.norm(Dodd)), float(np.max(np.abs(D)))

def lam2_lam3(Tj):
    w = np.linalg.eigvals(Tj); a = np.sort(np.abs(w))[::-1]
    return float(a[1]), float(a[2])

# ----------------------------------------------------------------------------- surrogate
def walk_fast(T, n, rng):
    """length-n Markov walk on len(T) states with transition T (3x3 or 9x9). tight cdf loop."""
    k = T.shape[0]
    cdf = np.cumsum(T, axis=1)
    u = rng.random(n)
    out = np.empty(n, dtype=np.int64)
    s = int(rng.integers(0, k))
    for i in range(n):
        out[i] = s
        r = u[i]; row = cdf[s]; nx = k - 1
        for j in range(k):
            if r < row[j]: nx = j; break
        s = nx
    return out

def surrogate_seq(T1, T2, n, rng):
    a = walk_fast(T1, n, rng); b = walk_fast(T2, n, rng)
    return [(C3[a[i]], C3[b[i]]) for i in range(n)]

def cell_stats(seq, rng):
    """returns dict: G2_real, mean/std/p999 of G2_surr, z_G2, eps_hat, z_odd, z_even,
    dev_real, dev_surr_mean, dev_ratio, l2, l3.  Applies identical pipeline to real + 40 surr."""
    Cj, C1, C2 = count_tables(seq)
    T1, T2 = norm_rows(C1), norm_rows(C2)
    Tj = norm_rows(Cj); Tf = tensor(T1, T2)
    G2r = g2_pooled(Cj)
    even_r, odd_r, dev_r = swap_channels(Tj, Tf)
    l2, l3 = lam2_lam3(Tj)
    n = len(seq)
    g2s, evens, odds, devs = [], [], [], []
    for _ in range(MSUR):
        sq = surrogate_seq(T1, T2, n, rng)
        Cjs, C1s, C2s = count_tables(sq)
        T1s, T2s = norm_rows(C1s), norm_rows(C2s)
        Tjs = norm_rows(Cjs); Tfs = tensor(T1s, T2s)
        g2s.append(g2_pooled(Cjs))
        e, o, d = swap_channels(Tjs, Tfs)
        evens.append(e); odds.append(o); devs.append(d)
    g2s = np.array(g2s); evens = np.array(evens); odds = np.array(odds); devs = np.array(devs)
    gm, gsd = g2s.mean(), g2s.std(ddof=1)
    z = (G2r - gm) / gsd if gsd > 0 else float('nan')
    eps = float(np.sqrt(max(0.0, G2r - gm) / n))
    zodd = (odd_r - odds.mean()) / odds.std(ddof=1) if odds.std(ddof=1) > 0 else float('nan')
    zeven = (even_r - evens.mean()) / evens.std(ddof=1) if evens.std(ddof=1) > 0 else float('nan')
    return dict(n=n, G2r=G2r, gm=gm, gsd=gsd, g999=float(np.percentile(g2s, 99.9)),
                z=z, eps=eps, zodd=zodd, zeven=zeven, dev_r=dev_r, dev_s=float(devs.mean()),
                dev_ratio=dev_r / devs.mean() if devs.mean() > 0 else float('nan'),
                l2=l2, l3=l3)

# ----------------------------------------------------------------------------- planted control
def stationary(T):
    w, V = np.linalg.eig(T.T)
    i = int(np.argmin(np.abs(w - 1.0)))
    v = np.real(V[:, i]); v = v / v.sum()
    return v

def analytic_eps(Tc):
    """analytic pooled coupling eps of a 9-state joint transition Tc:
    eps^2 = sum_s pi_s * sum_ij (P_s-E_s)^2/E_s ,  P_s = Tc[s] as 3x3, E_s its indep fit."""
    pi = stationary(Tc); e2 = 0.0
    for s in range(9):
        P = Tc[s].reshape(3, 3); tot = P.sum()
        if tot <= 0: continue
        rm = P.sum(1, keepdims=True); cm = P.sum(0, keepdims=True); E = rm @ cm / tot
        m = E > 0
        e2 += pi[s] * float(np.sum((P[m] - E[m]) ** 2 / E[m]))
    return float(np.sqrt(max(0.0, e2)))

def copy_kernel(T1):
    """K[s,(c1',c2')] = T1[c1, c1'] if c2'==c1' else 0  (maximal copy-coupling)."""
    K = np.zeros((9, 9))
    for si, (c1, c2) in enumerate(S9):
        for c1p in range(3):
            K[si, I9[(C3[c1p], C3[c1p])]] += T1[I3[c1], c1p]
    return K

def plant_cell(Tc, n, rng):
    seq_idx = walk_fast(Tc, n, rng)
    seq = [S9[i] for i in seq_idx]
    return cell_stats(seq, rng)

# ============================================================================= RUN
def main():
    rng = np.random.default_rng(SEED)
    log = []
    print("=" * 96)
    print("C_T COUPLING UNIVERSALITY v2  (prereg PREREG_ct_coupling_universality_v1.md)  seed", SEED)
    print("=" * 96)

    # ---- reference marginals at p=100003 (Axis 1 base) -------------------------------------
    P1 = 100003
    print(f"\n[setup] building p={P1} full orbit for Axis-1 generators + planted control ...")
    zx1, n1, state1 = orbit_xlifts(P1)
    base_seq = states_step(zx1, n1, state1, 1, 1, min(n1 - 1, 120000))
    _, C1b, C2b = count_tables(base_seq)
    T1b, T2b = norm_rows(C1b), norm_rows(C2b)
    print(f"          orbit n={n1};  marginal C_1 eigen-spectrum "
          f"{[f'{v:.3f}' for v in np.sort(np.abs(np.linalg.eigvals(T1b)))[::-1]]}")

    # ---- PLANTED CONTROL (informativeness gate; runs FIRST) --------------------------------
    print("\n" + "-" * 96)
    print("PLANTED CONTROL  (null is uninformative unless this fires per prereg S4/S5)")
    print("-" * 96)
    Tf_b = tensor(T1b, T2b); K = copy_kernel(T1b)
    # calibrate delta -> analytic eps, pick delta for eps = 2%, 1%, 0.5%
    grid = np.linspace(0.0, 1.0, 2001)
    eps_of = np.array([analytic_eps((1 - d) * Tf_b + d * K) for d in grid])
    def delta_for(target):
        return float(grid[int(np.argmin(np.abs(eps_of - target)))])
    d2, d1, d05 = delta_for(0.02), delta_for(0.01), delta_for(0.005)
    print(f"  copy-coupling delta->eps calibration (analytic): "
          f"eps=2%@delta={d2:.3f}, 1%@{d1:.3f}, 0.5%@{d05:.3f}  "
          f"(eps range over delta in [0,1]: {eps_of.min():.3f}..{eps_of.max():.3f})")
    plant_specs = [("eps~2%,n=131072", d2, 131072, (7, 12), "FIRE"),
                   ("eps~2%,n=5000",   d2, 5000,   (None, 2), "SILENT"),
                   ("eps~1%,n=131072", d1, 131072, (1.5, 3.5), "BORDERLINE"),
                   ("eps~0.5%,n=131072", d05, 131072, (None, 1.5), "SILENT")]
    plant_pass = True
    print(f"  {'spec':<20}{'delta':>7}{'eps_an':>8}{'n':>9}{'z_G2':>9}  expect  result")
    for name, d, n, win, tag in plant_specs:
        Tc = (1 - d) * Tf_b + d * K
        eps_an = analytic_eps(Tc)
        st = plant_cell(Tc, n, rng)
        lo, hi = win
        ok = ((lo is None or st['z'] >= lo) and (hi is None or st['z'] <= hi))
        plant_pass &= ok
        wtxt = f"[{'-inf' if lo is None else lo},{'inf' if hi is None else hi}]"
        print(f"  {name:<20}{d:>7.3f}{eps_an:>8.4f}{n:>9}{st['z']:>9.2f}  {wtxt:>9}  "
              f"{'PASS' if ok else 'FAIL'} ({tag})")
    # channel localization: copy vs anti-copy plant should load different swap channels
    Kanti = np.zeros((9, 9))
    for si, (c1, c2) in enumerate(S9):
        for c1p in range(3):
            Kanti[si, I9[(C3[c1p], C3[2 - c1p])]] += T1b[I3[c1], c1p]   # c2' = -c1'
    stc = plant_cell((1 - d2) * Tf_b + d2 * K, 131072, rng)
    sta = plant_cell((1 - d2) * Tf_b + d2 * Kanti, 131072, rng)
    print(f"  channel test @eps~2%,n=131072:  copy-coupling  z_odd={stc['zodd']:+.1f} "
          f"z_even={stc['zeven']:+.1f}   |  anti-copy  z_odd={sta['zodd']:+.1f} z_even={sta['zeven']:+.1f}")
    print(f"  => PLANTED CONTROL {'PASSED' if plant_pass else 'FAILED'}")
    if not plant_pass:
        print("\n*** FULL STOP (prereg S9): planted control did not fire as predicted; "
              "null is UNINFORMATIVE. No branch conclusion emitted. ***")

    # ---- AXIS 1: 8 generators at p=100003, fixed n=50000 -----------------------------------
    print("\n" + "-" * 96)
    print("AXIS 1  -- 8 generators [h]G at p=100003, fixed n=50000 (isolate generator at fixed n)")
    print("-" * 96)
    NW = 50000
    hs = []
    while len(hs) < 8:
        h = int(rng.integers(2, n1))
        if np.gcd(h, n1) == 1 and h not in hs: hs.append(h)
    print(f"  {'h':>8}{'gcd':>5}{'z_G2':>9}{'eps_hat':>9}{'z_odd':>8}{'z_even':>8}{'dev_ratio':>10}")
    ax1 = []
    for h in hs:
        seq = states_step(zx1, n1, state1, h, int(rng.integers(1, n1)), NW)
        st = cell_stats(seq, rng); ax1.append(st)
        print(f"  {h:>8}{int(np.gcd(h,n1)):>5}{st['z']:>9.2f}{st['eps']:>9.4f}"
              f"{st['zodd']:>+8.1f}{st['zeven']:>+8.1f}{st['dev_ratio']:>10.2f}")
    eps1 = np.array([s['eps'] for s in ax1])
    print(f"  eps_hat across generators: median={np.median(eps1):.4f} "
          f"spread=[{eps1.min():.4f},{eps1.max():.4f}]  "
          f"(+/-{100*(eps1.max()-eps1.min())/2/np.median(eps1):.0f}% about median)")

    # ---- AXIS 2: prime-order curves, log-spaced full orbits over [5000,131072] --------------
    print("\n" + "-" * 96)
    print("AXIS 2  -- prime-ORDER curves (full orbit), log-spaced n in [5000,131072]; every")
    print("           candidate logged (no silent filter); inclusion floor n>=5000")
    print("-" * 96)
    targets = [5000, 8500, 14500, 25000, 42000, 72000, 95000, 131072]
    chosen = []
    for tgt in targets:
        p = nextprime(tgt - 1)
        tries = 0
        while tries < 400:
            if p % 3 == 1:
                nE = curve_order(p)
                isp = isprime(nE)
                inband = 0.6 * tgt <= nE <= 2.0 * tgt and nE >= 5000
                log.append((tgt, p, nE, bool(isp), bool(inband)))
                if isp and inband and all(abs(nE - c[1]) > 3 for c in chosen):
                    chosen.append((p, nE)); break
            p = int(nextprime(p)); tries += 1
    print(f"  selected {len(chosen)} prime-order curves:")
    print(f"  {'p':>8}{'n=#E':>9}{'z_G2':>9}{'eps_hat':>9}{'z_odd':>8}{'z_even':>8}"
          f"{'dev_ratio':>10}{'l2':>7}{'l3':>7}")
    ax2 = []
    for p, nE in sorted(chosen, key=lambda t: t[1]):
        zx, n, state = orbit_xlifts(p)
        seq = [state(zx[k], zx[k + 1]) for k in range(1, n)]
        st = cell_stats(seq, rng); st['p'] = p; ax2.append(st)
        print(f"  {p:>8}{st['n']:>9}{st['z']:>9.2f}{st['eps']:>9.4f}{st['zodd']:>+8.1f}"
              f"{st['zeven']:>+8.1f}{st['dev_ratio']:>10.2f}{st['l2']:>7.3f}{st['l3']:>7.3f}")

    # ---- AXIS 2b: fixed n=20000 window per Axis-2 prime -------------------------------------
    print("\n" + "-" * 96)
    print("AXIS 2b -- fixed n=20000 window per prime (separate prime-specific from n-driven)")
    print("-" * 96)
    ax2b = []
    print(f"  {'p':>8}{'z_G2':>9}{'eps_hat':>9}")
    for p, nE in sorted(chosen, key=lambda t: t[1]):
        zx, n, state = orbit_xlifts(p)
        cnt = min(20000, n - 1)
        seq = [state(zx[k], zx[k + 1]) for k in range(1, cnt + 1)]
        st = cell_stats(seq, rng); st['p'] = p; ax2b.append(st)
        print(f"  {p:>8}{st['z']:>9.2f}{st['eps']:>9.4f}")
    eps2b = np.array([s['eps'] for s in ax2b])
    print(f"  eps_hat across primes @n=20000: median={np.median(eps2b):.4f} "
          f"spread=[{eps2b.min():.4f},{eps2b.max():.4f}]")

    # ---- DECISION (prereg S7/S9) -----------------------------------------------------------
    print("\n" + "=" * 96)
    print("DECISION  (n-scaling of surrogate-normalized z_G2 / eps_hat; Z*=5)")
    print("=" * 96)
    ns = np.array([s['n'] for s in ax2], float)
    zs = np.array([s['z'] for s in ax2], float)
    es = np.array([s['eps'] for s in ax2], float)
    ratios = np.array([s['dev_ratio'] for s in ax2], float)
    zclip = np.clip(zs, 0.3, None)
    slope_z = np.polyfit(np.log(ns), np.log(zclip), 1)[0]
    slope_e = np.polyfit(np.log(ns), np.log(es), 1)[0]
    zmax = zs[np.argmax(ns)]; G2max = ax2[int(np.argmax(ns))]['G2r']; g999 = ax2[int(np.argmax(ns))]['g999']
    zodd_arr = np.array([s['zodd'] for s in ax2]); zeven_arr = np.array([s['zeven'] for s in ax2])
    slope_odd = np.polyfit(np.log(ns), np.clip(zodd_arr, 0.3, None), 1)[0] if (zodd_arr > 0).any() else 0.0
    eps_univ = (eps1.max() - eps1.min()) / 2 / np.median(eps1) <= 0.30 and \
               (eps2b.max() - eps2b.min()) / 2 / np.median(eps2b) <= 0.30
    print(f"  Axis-2 fit:  log z_G2 ~ {slope_z:+.3f} * log n     log eps_hat ~ {slope_e:+.3f} * log n")
    print(f"  at n_max={int(ns.max())}: z_G2={zmax:.2f}  G2_real={G2max:.1f}  surr99.9pct={g999:.1f}")
    print(f"  dev_real/dev_surr range over Axis 2: [{ratios.min():.2f},{ratios.max():.2f}]")
    print(f"  eps_hat universal within +/-30% (Axis1 & Axis2b): {eps_univ}")
    print(f"  swap-odd channel slope: {slope_odd:+.3f}   (rising+crossing would trigger subspace)")

    branch = "?"
    if not plant_pass:
        branch = "FULL STOP -- planted control failed; verdict withheld"
    elif slope_z >= 0.5 and zmax >= 5 and G2max > g999 and eps_univ:
        branch = "A -- UNIVERSAL NONZERO COUPLING"
    elif zmax < 5 and slope_z < 0.5 and abs(slope_e + 0.5) <= 0.2 and ratios.min() >= 0.5 \
            and ratios.max() <= 2.0 and (zodd_arr.max() < 5 and zeven_arr.max() < 5):
        branch = "B -- UNIVERSAL NOISE FLOOR (coupling bounded < ~1.35% at n~1.3e5, b=7, p<=2^17)"
    elif zmax >= 5 and not eps_univ:
        branch = "C -- GENERATOR/PRIME-SPECIFIC coupling"
    elif zmax < 5 and (slope_z >= 0.5 or slope_odd >= 0.5):
        branch = "D -- UNDERPOWERED at 2^17; extend p (do NOT call floor)"
    elif zmax < 5 and zodd_arr.max() >= 5:
        branch = "A/subspace -- coupling in swap-odd channel; report it"
    else:
        branch = "B* -- floor-consistent but check edge conditions manually (see numbers above)"
    print("\n  >>> BRANCH:", branch)
    print("  (All numbers scope: b=7, p<=2^17~1.3e5, pooled-G2/swap estimators, this seed. "
          "No power below ~1.35%, zero power at 2^256 -- prereg S5/S6.)")

    # candidate log (anti-defect: every p seen, with reason)
    print("\n" + "-" * 96)
    print("AXIS-2 CANDIDATE LOG (target, p, #E, #E prime?, in-band?) -- no silent filter")
    for r in log:
        print(f"    tgt={r[0]:>7}  p={r[1]:>7}  #E={r[2]:>7}  prime={str(r[3]):>5}  inband={r[4]}")


if __name__ == "__main__":
    main()
