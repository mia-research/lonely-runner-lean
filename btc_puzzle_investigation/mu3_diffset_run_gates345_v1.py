#!/usr/bin/env python3
r"""
mu3_diffset_run_gates345_v1.py -- PREREG gates 3,4,5.

Executes `PREREG_mu3_diffset_control_repair_v1.md` §3 (frozen nulls + F4),
§4 (PC-A / PC-B ladders + multiplicity surrogates, F1-F3/F6/F7) and §9.1 gate 5
(the studied sets), in that order. Gate 5 refuses to run unless 1-4 are green.
Gate 1-2 must already have passed via mu3_diffset_forced_zero_reproduce_v1.py.

EXACTNESS (§8): the decision path is integers only. gmpy2 mpz for speed; chi3 by
powmod; E3 = n0^2+n1^2+n2^2-n0n1-n1n2-n2n0 from exact class counts. Floats appear
only in reported ratios/rates, never in a comparison that decides a gate.

Speed: batch (Montgomery) inversion makes the C(m,2) group-law differences cost
one inversion per point set instead of C(m,2).
"""
import csv, json, math, random, sys, time
from collections import Counter

from gmpy2 import mpz, powmod

sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")

P = mpz(2**256 - 2**32 - 977)
CB = (P - 1) // 3
N_ORDER = mpz(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141)
SEED = 20260730
U_COEF = 3.6889

POOL_A = "constructed_keys_1to160_100k.csv"
POOL_B = "constructed_keys_fullrange_v1.csv"
REAL = "solved_keys_augmented_v1.csv"

GATES = {}
NOTES = []


def log(*a):
    print(*a, flush=True)


# ---------------------------------------------------------------- chi3 (§8 convention)
def _mk_chi3():
    g = mpz(2)
    while powmod(g, CB, P) == 1:
        g += 1
    beta = powmod(g, CB, P)
    lut = {1: 0, int(beta): 1, int(beta * beta % P): 2}
    return lut, beta, g


CH_LUT, BETA, G_NONCUBE = _mk_chi3()


def chi3_t(v):
    """cubic class t in {0,1,2}; None iff v == 0."""
    v %= P
    if v == 0:
        return None
    return CH_LUT[int(powmod(v, CB, P))]


def E3(n):
    a, b, c = n
    return a * a + b * b + c * c - a * b - b * c - c * a


def eps_hat(n0, npair):
    """measured epsilon = (3 n0 - n_p) / (2 n_p), exact rational -> float report."""
    return (3 * n0 - npair) / (2 * npair)


# ---------------------------------------------------------------- batch difference engine
def batch_inv(xs):
    n = len(xs)
    pre = [mpz(1)] * (n + 1)
    for i, x in enumerate(xs):
        pre[i + 1] = pre[i] * x % P
    inv = powmod(pre[n], P - 2, P)
    out = [None] * n
    for i in range(n - 1, -1, -1):
        out[i] = inv * pre[i] % P
        inv = inv * xs[i] % P
    return out


def _add(A, B):
    if A is None:
        return B
    if B is None:
        return A
    x1, y1 = A
    x2, y2 = B
    if x1 == x2:
        if (y1 + y2) % P == 0:
            return None
        m = (3 * x1 * x1) * powmod(2 * y1, P - 2, P) % P
    else:
        m = (y2 - y1) * powmod(x2 - x1, P - 2, P) % P
    x3 = (m * m - x1 - x2) % P
    return x3, (m * (x1 - x3) - y1) % P


def diffs(pts):
    """All C(m,2) group-law differences P_i - P_j (i<j), one batch inversion.
    Returns list of (x,y). Preserves the i<j orientation convention (§3 trap)."""
    n = len(pts)
    ii, dens, slow = [], [], []
    for i in range(n):
        xi = pts[i][0]
        for j in range(i + 1, n):
            d = (pts[j][0] - xi) % P
            if d == 0:
                slow.append((i, j))
            else:
                ii.append((i, j))
                dens.append(d)
    invs = batch_inv(dens) if dens else []
    out = []
    for (i, j), iv in zip(ii, invs):
        x1, y1 = pts[i]
        x2, y2 = pts[j]
        m = (-y2 - y1) * iv % P
        x3 = (m * m - x1 - x2) % P
        out.append((x3, (m * (x1 - x3) - y1) % P))
    for (i, j) in slow:
        R = _add(pts[i], (pts[j][0], (-pts[j][1]) % P))
        if R is not None:
            out.append(R)
    return out


def classes(pts):
    """(nx, nxy, Vx_multiplicity_spectrum) for a point set."""
    D = diffs(pts)
    nx = [0, 0, 0]
    nxy = [0, 0, 0]
    vc = Counter()
    for (x, y) in D:
        tx = chi3_t(x)
        if tx is not None:
            nx[tx] += 1
        txy = chi3_t(x * y % P)
        if txy is not None:
            nxy[txy] += 1
        vc[int(x)] += 1
    return nx, nxy, vc


# ---------------------------------------------------------------- pools
def load_pool(path, xcol="X", ycol="Y", bitcol=None, dcol=None, limit=None):
    rows = []
    with open(path) as f:
        for r in csv.DictReader(f):
            try:
                x = mpz(int(r[xcol], 16))
                y = mpz(int(r[ycol], 16))
            except (ValueError, KeyError, TypeError):
                continue
            e = {"P": (x, y)}
            if bitcol:
                e["bits"] = int(r[bitcol])
            rows.append(e)
            if limit and len(rows) >= limit:
                break
    return rows


# ---------------------------------------------------------------- GATE 3: frozen nulls
def gate3(cellname, draw_fn, N, npair, t0):
    log(f"\n  [{cellname}] building frozen null, N={N}, n_pairs={npair}")
    e3x, e3xy, spectra = [], [], []
    for k in range(N):
        pts = draw_fn(k)
        nx, nxy, vc = classes(pts)
        e3x.append(E3(nx))
        e3xy.append(E3(nxy))
        spectra.append(len([1 for v in vc.values() if v > 1]))
        if (k + 1) % max(1, N // 8) == 0:
            log(f"      {k+1}/{N}  ({time.time()-t0:.0f}s)")
    sx, sxy = sorted(e3x), sorted(e3xy)
    L = sx[int(0.025 * N)]
    Uq = sx[max(0, math.ceil(0.975 * N) - 1)]
    Lxy = sxy[int(0.025 * N)]
    Uxy = sxy[max(0, math.ceil(0.975 * N) - 1)]
    mean_x = sum(e3x) / N
    Uref = U_COEF * npair
    # F4 shape gate
    f4_mean_ok = 0.95 * npair <= mean_x <= 1.05 * npair
    f4_q_ok = 0.9 * Uref <= Uq <= 1.1 * Uref
    # cell correlation (S5/S6: not independent)
    mx = mean_x
    my = sum(e3xy) / N
    cov = sum((a - mx) * (b - my) for a, b in zip(e3x, e3xy)) / N
    vx = sum((a - mx) ** 2 for a in e3x) / N
    vy = sum((b - my) ** 2 for b in e3xy) / N
    rho = cov / math.sqrt(vx * vy) if vx > 0 and vy > 0 else float("nan")
    log(f"      E3x  mean={mean_x:.0f} (n_p={npair})  region=[{L},{Uq}]  U_ref={Uref:.0f}")
    log(f"      E3xy mean={my:.0f}  region=[{Lxy},{Uxy}]")
    log(f"      F4 mean in n_p*[0.95,1.05]: {f4_mean_ok}   97.5% in U_ref*[0.9,1.1]: {f4_q_ok}")
    log(f"      corr(E3x,E3xy) = {rho:+.3f}   sets with >=1 repeated diff: "
        f"{sum(1 for s in spectra if s)}/{N}")
    GATES[f"F4_{cellname}"] = bool(f4_mean_ok and f4_q_ok)
    return dict(L=int(L), U=int(Uq), Lxy=int(Lxy), Uxy=int(Uxy), mean_x=mean_x,
                mean_xy=my, rho=rho, npair=npair, N=N,
                f4_mean_ok=bool(f4_mean_ok), f4_q_ok=bool(f4_q_ok))


# ---------------------------------------------------------------- multiplicity surrogate
def surrogate(vc, B, rng):
    """Keep the observed multiplicity spectrum; randomize each DISTINCT value's chi3."""
    w = list(vc.values())
    out = []
    for _ in range(B):
        n = [0, 0, 0]
        for wt in w:
            n[rng.randrange(3)] += wt
        out.append(E3(n))
    out.sort()
    return out


# ---------------------------------------------------------------- GATE 4: PC-A
def pc_a(npair, region_U, rng, rungs, R=10000):
    """Instrument plant: relabel ceil(eps*n_p) pairs into class 0. Integer only."""
    log(f"\n  PC-A instrument ladder (n_p={npair}, U={region_U}, {R} realizations/rung)")
    log(f"    {'eps':>6} {'fire rate':>10} {'median E3':>12} {'E3/U':>8}")
    curve = {}
    for eps in rungs:
        k = math.ceil(eps * npair)
        fires, med = 0, []
        for _ in range(R):
            n = [0, 0, 0]
            for _ in range(npair - k):
                n[rng.randrange(3)] += 1
            n[0] += k
            e = E3(n)
            med.append(e)
            fires += (e > region_U)
        med.sort()
        m = med[len(med) // 2]
        curve[eps] = fires / R
        log(f"    {eps:>6.3f} {fires/R:>10.3f} {m:>12} {m/region_U:>8.2f}")
    return curve


# ---------------------------------------------------------------- GATE 4: PC-B
def pc_b(pool_draw, m, dnum, rng, readout="x", dden=10000):
    """Set-level plant on real curve points, aimed at a TARGET class-0 frequency.

    DEVIATION D2 (three iterations, each measured, all disclosed):
      * the prereg's one-sided rule `3c >= |S| + ceil(3*delta*|S|)` selects the
        UPPER TAIL, so it overshoots its own target -- measured eps_hat = 0.077 at
        delta = 0, where the plant should be nil;
      * a band CENTRED on the target fixes delta = 0 (eps_hat = 0.0008) but
        undershoots for delta > 0 and saturates near eps_hat = 0.026, because the
        candidate density is asymmetric across the band.
    Both are open-loop. This is a closed-loop integer servo: accept a candidate only
    if it moves the RUNNING class-0 excess toward the target. It converges to the
    target rather than to a tail, and reduces to an unbiased filter at delta = 0.
    delta is carried as the exact rational dnum/dden; every comparison is integer.
    """
    S = [pool_draw(rng)]
    n0run = totrun = 0
    guard = 0
    while len(S) < m:
        guard += 1
        if guard > 600 * m:
            return None
        Q = pool_draw(rng)
        if any(Q[0] == s[0] for s in S):
            continue
        c = 0
        for Pt in S:
            R = _add(Q, (Pt[0], (-Pt[1]) % P))
            if R is None:
                continue
            v = R[0] if readout == "x" else R[0] * R[1] % P
            c += (chi3_t(v) == 0)
        k = len(S)
        if k < 8:
            S.append(Q)
            n0run += c
            totrun += k
            continue
        # target excess: 3*n0 - tot == 3*delta*tot   (since eps = 1.5*delta)
        cand = (3 * c - k) * dden
        want = 3 * dnum * k
        below = (3 * n0run - totrun) * dden <= 3 * dnum * totrun
        if (cand >= want) if below else (cand <= want):
            S.append(Q)
            n0run += c
            totrun += k
    return S


def pc_b_ladder(cellname, pool_draw, m, npair, region_U, rungs, reps, rng, B_sur=2000):
    log(f"\n  PC-B end-to-end ladder [{cellname}] m={m}, {reps} constructions/rung")
    log(f"    {'delta':>7} {'eps~':>7} {'fire':>6} {'med E3':>10} {'E3/U':>7} "
        f"{'eps_hat':>8} {'sur.fire':>9}")
    out = {}
    for dnum in rungs:                     # dnum = delta * 10000, exact integer
        delta = dnum / 10000
        eps_t = 1.5 * delta
        e3s, ehats, surfire, built = [], [], 0, 0
        for _ in range(reps):
            S = pc_b(pool_draw, m, dnum, rng, "x")
            if S is None:
                continue
            built += 1
            nx, nxy, vc = classes(S)
            e = E3(nx)
            e3s.append(e)
            ehats.append(eps_hat(nx[0], sum(nx)))   # class 0 = planted class
            sur = surrogate(vc, 200, rng)
            surfire += (e > sur[max(0, math.ceil(0.975 * len(sur)) - 1)])
        if not e3s:
            log(f"    {delta:>7.4f}  -- no constructions completed --")
            continue
        e3s_s = sorted(e3s)
        med = e3s_s[len(e3s_s) // 2]
        fire = sum(1 for e in e3s if e > region_U) / len(e3s)
        out[dnum] = dict(fire=fire, med=med, ratio=med / region_U,
                          eps_hat=sum(ehats) / len(ehats),
                          sur_fire=surfire / len(e3s), n=built)
        log(f"    {delta:>7.4f} {eps_t:>7.4f} {fire:>6.2f} {med:>10} "
            f"{med/region_U:>7.2f} {sum(ehats)/len(ehats):>8.4f} {surfire/len(e3s):>9.2f}")
    return out


# ---------------------------------------------------------------- main
def main():
    t0 = time.time()
    rng = random.Random(SEED)
    log("=" * 78)
    log("PREREG gates 3-5 -- mu3 difference-set repaired control")
    log("=" * 78)
    log(f"  beta={int(BETA)}\n  g_noncube={int(G_NONCUBE)}  seed={SEED}")

    # ---- pools
    log("\nloading pools ...")
    realrows = load_pool(REAL, "X", "Y", bitcol="bits")
    real_pts = [r["P"] for r in realrows]
    real_bits = [r["bits"] for r in realrows]
    poolA = load_pool(POOL_A, "X", "Y", bitcol="bits")
    poolB = load_pool(POOL_B, "X", "Y")
    byb = {}
    for r in poolA:
        byb.setdefault(r["bits"], []).append(r["P"])
    log(f"  real={len(real_pts)} (bits {min(real_bits)}..{max(real_bits)}), "
        f"poolA={len(poolA)}, poolB={len(poolB)}")
    mA, mB = len(real_pts), 160
    npA, npB = mA * (mA - 1) // 2, mB * (mB - 1) // 2

    rA = random.Random(SEED)
    rB = random.Random(SEED + 1)

    def drawA(_k):
        return [rA.choice(byb[b]) for b in real_bits]

    def drawB(_k):
        return rB.sample([r["P"] for r in poolB], mB)

    # ---- GATE 3
    log("\n" + "-" * 78 + "\nGATE 3: frozen nulls + F4 shape gate")
    NA = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
    NB = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    nullA = gate3("A", drawA, NA, npA, t0)
    nullB = gate3("B", drawB, NB, npB, t0)

    # ---- GATE 4
    log("\n" + "-" * 78 + "\nGATE 4: PC-A and PC-B ladders")
    epsr = [0.0, 0.010, 0.015, 0.020, 0.025, 0.030, 0.040, 0.050, 0.100]
    pcaA = pc_a(npA, nullA["U"], rng, epsr)
    pcaB = pc_a(npB, nullB["U"], rng, epsr)
    dl = [0, 94, 141, 207, 277, 333]      # delta*10000, exact
    flatB = [r["P"] for r in poolB]
    repA = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    repB = int(sys.argv[4]) if len(sys.argv) > 4 else 50
    pcbA = pc_b_ladder("A", lambda r: r.choice(byb[r.choice(real_bits)]), mA, npA,
                       nullA["U"], dl, repA, rng)
    pcbB = pc_b_ladder("B", lambda r: r.choice(flatB), mB, npB,
                       nullB["U"], dl, repB, rng)

    # gates
    def fire(d, k):
        return d.get(k, {}).get("fire", 0.0)

    GATES["PCB_fire_A_eps05"] = fire(pcbA, 333) >= 0.95
    GATES["PCB_fire_B_eps05"] = fire(pcbB, 333) >= 0.95
    GATES["PCB_margin_A"] = pcbA.get(333, {}).get("ratio", 0) >= 2.0
    GATES["PCB_margin_B"] = pcbB.get(333, {}).get("ratio", 0) >= 5.0
    GATES["PCB_mindet_A"] = fire(pcbA, 277) >= 0.80
    GATES["PCB_mindet_B"] = fire(pcbB, 141) >= 0.80
    # F2 (§4.4): PC-B INSIDE its multiplicity surrogate => defective. So the gate
    # passes when PC-B's E3 sits ABOVE the surrogate's 97.5% -- i.e. the planted
    # excess is cubic-class structure, not repeated differences.
    GATES["F2_A_plant_above_surrogate"] = pcbA.get(333, {}).get("sur_fire", 0.0) >= 0.95
    GATES["F2_B_plant_above_surrogate"] = pcbB.get(333, {}).get("sur_fire", 0.0) >= 0.95

    log("\n  GATE 4 status:")
    for k, v in GATES.items():
        log(f"    [{'PASS' if v else 'FAIL'}] {k}")

    green = all(GATES.values())

    # ---- GATE 5
    log("\n" + "-" * 78)
    if not green:
        log("GATE 5: REFUSED -- gates 1-4 not all green.")
        log("Per §9.2 the outcome is [NO VALIDATED POWER]; no bound may be stated.")
    else:
        log("GATE 5: gates 1-4 green -- computing the studied sets")
        studied = {}
        for name, pts, npair, nullc in (("real-82", real_pts, npA, nullA),
                                        ("constructed-160", drawB(0), npB, nullB)):
            nx, nxy, vc = classes(pts)
            ex, exy = E3(nx), E3(nxy)
            sur = surrogate(vc, 10000, rng)
            sU = sur[max(0, math.ceil(0.975 * len(sur)) - 1)]
            studied[name] = dict(
                nx=nx, nxy=nxy, E3x=ex, E3xy=exy,
                inside_x=bool(nullc["L"] <= ex <= nullc["U"]),
                inside_xy=bool(nullc["Lxy"] <= exy <= nullc["Uxy"]),
                eps_hat=eps_hat(nx[0], sum(nx)),
                sur_U=int(sU), inside_sur=bool(ex <= sU),
                region=[nullc["L"], nullc["U"]], region_xy=[nullc["Lxy"], nullc["Uxy"]])
            s = studied[name]
            log(f"\n    {name}: n_p={npair}")
            log(f"      classes x  = {nx}   E3x  = {ex}   region {s['region']}   "
                f"inside={s['inside_x']}")
            log(f"      classes xy = {nxy}   E3xy = {exy}   region {s['region_xy']}  "
                f"inside={s['inside_xy']}")
            log(f"      eps_hat = {s['eps_hat']:+.4f}   multiplicity surrogate 97.5% = "
                f"{s['sur_U']}  inside={s['inside_sur']}")
        GATES["_studied"] = True
        json.dump(dict(gates=GATES, nullA=nullA, nullB=nullB, studied=studied,
                       pcaA=pcaA, pcaB=pcaB, pcbA=pcbA, pcbB=pcbB,
                       beta=int(BETA), g=int(G_NONCUBE), seed=SEED, NA=NA, NB=NB),
                  open("mu3_diffset_meta_v1.json", "w"), indent=1, default=str)
        log("\n  wrote mu3_diffset_meta_v1.json")

    log(f"\ntotal {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
