#!/usr/bin/env python3
"""
flap_a_invariance_v1.py -- execute PREREG_flap_a_invariance_v1.md.

Is the doubling 2x2 (eps_a(X), eps_a(x2(X))) INVARIANT across the classifier multiplier a?
The completed run (flap_grouplaw_run_v1.out) used ONE fixed a and returned null.  Here K distinct
mu6-orbits of a are drawn; the primary statistic is the exact-integer DISPERSION of the per-a
2x2 deviation across a, ranked against the joint conditional permutation null (Null-P).

Classifier = AS-IMPLEMENTED absolute-value form (prereg 0.1):  eps_a(X)=1 iff 2|cent(aX)-cent(rho aX)|>p.
Signal path exact int.  numpy touches only uint8 0/1 label matrices.  Usage: flap_a_invariance_v1.py [n] [B]
"""
import sys, random, hashlib
import numpy as np
from avenue5_only import p

BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
RHO = (BETA + 1) % p
assert pow(BETA, 3, p) == 1 and (RHO * RHO - RHO + 1) % p == 0
B2 = BETA * BETA % p
SEED_A = 20260723
SEED_POOL = 424242
SEED_GATE = 20260721
K = 32
ALPHA_NUM, ALPHA_DEN = 1, 60          # alpha* = 1/60


def cent(u):
    u %= p
    return u - p if u > (p - 1) // 2 else u


def eps_a(a, X):
    s = a * X % p
    return 1 if 2 * abs(cent(s) - cent(RHO * s % p)) > p else 0


def eps_a_signed(a, X):                # for the 0.1 record only
    s = a * X % p
    return 1 if 2 * (cent(s) - cent(RHO * s % p)) > p else 0


def batch_inv(vals):
    if not vals:
        return []
    pref = [1] * (len(vals) + 1)
    for i, v in enumerate(vals):
        pref[i + 1] = pref[i] * v % p
    inv = pow(pref[-1], p - 2, p)
    out = [0] * len(vals)
    for i in range(len(vals) - 1, -1, -1):
        out[i] = pref[i] * inv % p
        inv = inv * vals[i] % p
    return out


def sample_a():
    """K values of a, uniform, bit_length>=200, pairwise mu6-orbit-distinct.  Frozen by SEED_A."""
    rng = random.Random(SEED_A)
    seen = set()
    out = []
    while len(out) < K:
        a = rng.randrange(1, p)
        if a.bit_length() < 200:
            continue
        orb = {a, (p - a) % p, BETA * a % p, (p - BETA * a % p) % p,
               B2 * a % p, (p - B2 * a % p) % p}
        if orb & seen:
            continue
        seen |= orb
        out.append(a)
    return out


def build_pool(n, seed):
    """n valid abscissas X with their doubling images x2(X).  Guards: 2-torsion, 3-torsion."""
    rng = random.Random(seed)
    Xs, dens, nums = [], [], []
    while len(Xs) < n:
        X = rng.randrange(1, p)
        rhs = (X * X % p * X + 7) % p
        if rhs == 0 or pow(rhs, (p - 1) // 2, p) != 1:
            continue
        den = 4 * rhs % p
        if den == 0:
            continue
        Xs.append(X); dens.append(den)
        nums.append((pow(X, 4, p) - 56 * X) % p)
    invs = batch_inv(dens)
    X2 = [nums[i] * invs[i] % p for i in range(n)]
    keep = [i for i in range(n) if X2[i] != Xs[i]]        # 3-torsion guard
    return [Xs[i] for i in keep], [X2[i] for i in keep]


def labels(As, Xs, X2s):
    n = len(Xs)
    DOM = np.zeros((len(As), n), dtype=np.uint8)
    IMG = np.zeros((len(As), n), dtype=np.uint8)
    for ai, a in enumerate(As):
        DOM[ai] = np.fromiter((eps_a(a, X) for X in Xs), dtype=np.uint8, count=n)
        IMG[ai] = np.fromiter((eps_a(a, X) for X in X2s), dtype=np.uint8, count=n)
    return DOM, IMG


def dev_vector(DOM, IMG, perm=None):
    """dev_a = n*FF_a - rowF_a*colF_a, exact Python ints."""
    n = DOM.shape[1]
    rowF = DOM.sum(axis=1, dtype=np.int64)
    colF = IMG.sum(axis=1, dtype=np.int64)
    J = IMG if perm is None else IMG[:, perm]
    FF = np.bitwise_and(DOM, J).sum(axis=1, dtype=np.int64)
    return [int(n) * int(FF[i]) - int(rowF[i]) * int(colF[i]) for i in range(DOM.shape[0])]


def stats(dev):
    """DEVIATION D1 (see PREREG_flap_a_invariance_v1_DEVIATIONS.md).  The frozen spec's
    D_int = sum(dev_a^2) is an UNCENTRED sum of squares, so a shift common to every a inflates it;
    its own PC-dep-NEG control fired, VOIDing it as a dispersion statistic.  Replaced by the
    CENTRED form, kept in exact integers by scaling with K:
        D_cen = K*sum(dev^2) - (sum dev)^2   == K^2 * (centred sum of squares)
        M_cen = max_a |K*dev_a - sum(dev)|   == K * max_a |dev_a - mean|
    theta-bar (S_pool) stays UNCENTRED -- it is a mean statistic and MUST fire under PC-dep-NEG."""
    k = len(dev)
    s = sum(dev)
    D_cen = k * sum(d * d for d in dev) - s * s
    M_cen = max(abs(k * d - s) for d in dev)
    return D_cen, M_cen, abs(s)


def fires(rank, B):
    """integer comparison of p=(1+rank)/(B+1) against alpha*=1/60, no float."""
    return (1 + rank) * ALPHA_DEN <= ALPHA_NUM * (B + 1)


def main():
    n_req = int(sys.argv[1]) if len(sys.argv) > 1 else 1000000
    B = int(sys.argv[2]) if len(sys.argv) > 2 else 9999

    # ---- ordering enforcement: a-sample written + hashed BEFORE the pool exists
    As = sample_a()
    blob = "\n".join(hex(a) for a in As).encode()
    with open("a_sample_v1.txt", "w") as fh:
        fh.write("\n".join(hex(a) for a in As) + "\n")
    print("# a-sample K=%d  sha256=%s" % (len(As), hashlib.sha256(blob).hexdigest()))
    A_plant = set(range(K // 4))                    # first K/4 entries, fixed in advance

    # ---- ARM 0 gates
    print("\n=== ARM 0 GATE ===")
    grng = random.Random(SEED_GATE)
    gate = []
    while len(gate) < 4096:
        X = grng.randrange(1, p)
        rhs = (X * X % p * X + 7) % p
        if rhs and pow(rhs, (p - 1) // 2, p) == 1:
            gate.append(X)
    g2_bad = 0
    dens_abs, dens_sgn = [], []
    for a in As:
        nf = 0
        for X in gate:
            e = eps_a(a, X)
            nf += e
            if not (e == eps_a(a, BETA * X % p) == eps_a(a, B2 * X % p) == eps_a(a, (p - X) % p)):
                g2_bad += 1
        dens_abs.append(nf)
        dens_sgn.append(sum(eps_a_signed(a, X) for X in gate))
    ng = len(gate)
    from math import isqrt
    g3_bad = [i for i, nf in enumerate(dens_abs) if abs(4 * nf - ng) > 6 * isqrt(3 * ng)]
    print("  G2 mu6-invariance exceptions = %d / %d  (need 0)" % (g2_bad, K * ng))
    print("  G3 quarter-density failures  = %d / %d   [abs-form mean=%.5f  signed-form mean=%.5f]"
          % (len(g3_bad), K, sum(dens_abs) / (K * ng), sum(dens_sgn) / (K * ng)))
    print("  G6 mu6-orbit distinctness    = enforced at sampling (K=%d distinct configurations)" % K)
    if g2_bad or g3_bad:
        print("  *** ARM 0 FAILED -> VOID, no verdict ***"); return

    # ---- pool
    print("\n=== POOL ===")
    Xs, X2s = build_pool(n_req, SEED_POOL)
    n = len(Xs)
    print("  n = %d valid abscissas (after 2/3-torsion guards)" % n)
    # G5: independent doubling check
    bad5 = 0
    for X, X2 in list(zip(Xs, X2s))[:200]:
        y2 = (X * X % p * X + 7) % p
        y = pow(y2, (p + 1) // 4, p)
        lam = 3 * X * X % p * pow(2 * y, p - 2, p) % p
        if (lam * lam - 2 * X) % p != X2:
            bad5 += 1
    print("  G5 x2 vs independent affine doubling: %d/200 mismatches (need 0)" % bad5)
    if bad5:
        print("  *** G5 FAILED -> VOID ***"); return

    DOM, IMG = labels(As, Xs, X2s)

    # ---- PC-max and PC-id (forced gates)
    IMGb = np.zeros_like(DOM)
    for ai, a in enumerate(As):
        IMGb[ai] = np.fromiter((eps_a(a, BETA * X % p) for X in Xs), dtype=np.uint8, count=n)
    pcmax_bad = int(np.count_nonzero(IMGb != DOM))
    DOMba = np.zeros_like(DOM)
    IMGba = np.zeros_like(DOM)
    for ai, a in enumerate(As):
        ab = BETA * a % p
        DOMba[ai] = np.fromiter((eps_a(ab, X) for X in Xs), dtype=np.uint8, count=n)
        IMGba[ai] = np.fromiter((eps_a(ab, X) for X in X2s), dtype=np.uint8, count=n)
    pcid_bad = int(np.count_nonzero(DOMba != DOM)) + int(np.count_nonzero(IMGba != IMG))
    print("\n=== FORCED GATES ===")
    print("  PC-max  (X->betaX forced diagonal) off-diagonal cells = %d  -> %s"
          % (pcmax_bad, "FIRES" if pcmax_bad == 0 else "*** FAILED -> VOID ***"))
    print("  PC-id   (table for a vs beta*a identical) exceptions   = %d  -> %s"
          % (pcid_bad, "PASS" if pcid_bad == 0 else "*** FAILED -> VOID ***"))
    if pcmax_bad or pcid_bad:
        return

    # ---- observed statistics + Null-P
    rng = np.random.default_rng(20260723)
    dev = dev_vector(DOM, IMG)
    D_obs, M_obs, S_obs = stats(dev)
    rk_D = rk_M = rk_S = 0
    nullD = []
    for b in range(B):
        perm = rng.permutation(n)
        d2, m2, s2 = stats(dev_vector(DOM, IMG, perm))
        nullD.append(d2)
        if d2 >= D_obs: rk_D += 1
        if m2 >= M_obs: rk_M += 1
        if s2 >= S_obs: rk_S += 1

    print("\n=== T1 tables (per a) ===")
    rowF = DOM.sum(axis=1, dtype=np.int64); colF = IMG.sum(axis=1, dtype=np.int64)
    FF = np.bitwise_and(DOM, IMG).sum(axis=1, dtype=np.int64)
    import math
    thetas = []
    for i in range(K):
        cf = int(colF[i] - FF[i]); fc = int(rowF[i] - FF[i])
        cc = n - int(FF[i]) - cf - fc
        th = math.log(cc * int(FF[i]) / (cf * fc)) if cf and fc and cc and FF[i] else float('nan')
        thetas.append(th)
    tbar = sum(thetas) / K
    tsd = (sum((t - tbar) ** 2 for t in thetas) / (K - 1)) ** 0.5
    print("  theta_a: mean=%+.5f  sd=%.5f  min=%+.5f  max=%+.5f" % (tbar, tsd, min(thetas), max(thetas)))

    print("\n=== PRIMARY / SECONDARY (Null-P, B=%d, alpha*=1/60) ===" % B)
    for nm, rk, ob in (("D_int (PRIMARY dispersion)", rk_D, D_obs),
                       ("M_max (sparse alt)", rk_M, M_obs),
                       ("theta-bar (pooled mean)", rk_S, S_obs)):
        print("  %-28s rank=%5d  p=(1+%d)/(%d)  -> %s"
              % (nm, rk, rk, B + 1, "FIRES" if fires(rk, B) else "null"))

    # ---- PC-dep-arith: a in A_plant get the forced-diagonal image => genuine a-dependence
    IMGp = IMG.copy()
    for ai in A_plant:
        IMGp[ai] = IMGb[ai]
    devp = dev_vector(DOM, IMGp)
    Dp, Mp, _ = stats(devp)
    rkDp = sum(1 for d in nullD if d >= Dp)
    print("\n=== PLANTED CONTROLS ===")
    print("  PC-dep-arith (|A_plant|=%d forced-diagonal) D_int rank=%d -> %s"
          % (len(A_plant), rkDp, "FIRES" if fires(rkDp, B) else "*** FAILED -> VOID ***"))

    # ---- PC-dep-NEG: same theta planted in EVERY a => no dispersion, but pooled mean must move
    IMGn = IMG.copy()
    m = n // 8
    for ai in range(K):
        IMGn[ai, :m] = DOM[ai, :m]
    devn = dev_vector(DOM, IMGn)
    Dn, Mn, Sn = stats(devn)
    rkDn = sum(1 for d in nullD if d >= Dn)
    rkSn = 0
    print("  PC-dep-NEG   (h=K, common shift)         D_int rank=%d -> %s  [must NOT fire]"
          % (rkDn, "FIRES" if fires(rkDn, B) else "null"))

    # ---- PC-FP: 100 pure Null-P realizations ranked against the same ensemble
    fp = 0
    for _ in range(100):
        perm = rng.permutation(n)
        d2, _, _ = stats(dev_vector(DOM, IMG, perm))
        if sum(1 for d in nullD if d >= d2) * ALPHA_DEN <= ALPHA_NUM * (B + 1):
            fp += 1
    print("  PC-FP        false-positive rate = %d/100  (need <= 3/100 = 2*alpha*)" % fp)
    print("FLAP_A_DONE")


if __name__ == '__main__':
    main()
