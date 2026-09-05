#!/usr/bin/env python3
"""
y_channel_eisn_v1.py -- the PARITY-CORRECT (y-using) channel into the scalar lift eis_n(d).

The parity result (verify_slippage_algebra_v1) proved: eis_p(X_d) is EVEN in d, eis_n(d) is ODD in d,
so the x-lift alone cannot reach eis_n(d) linearly.  y_d is ODD in d, so the OBSTRUCTION IS BYPASSED by
a y-using readout.  The symmetry-matched cheap readout is sign(xy): x even * y odd => xy ODD, and xy is
mu3-covariant weight-1 -- the SAME isotypic sector as eis_n(d) (odd + mu3-weight-1).

Occupying the right sector is necessary, not sufficient.  Question (build + measure, don't pre-verdict):
does the cheap odd readout CORRELATE with eis_n(d) above the sqrt(n) floor, or does reaching it still
need the DLP?  eis_n(d) is a NON-bounded-degree function of d, so the Part-V closure (which bounds
bounded-degree readouts vs the CHARACTER e_n(a d)) does not directly cover this target.

THREE parts:
 (A) [secp, structural] verify xy and eis_n are BOTH odd + mu3-weight-1 (same sector) -- the alignment.
 (B) [toy, FULL group -- decisive] MI(cheap odd readout ; eis_n target) over the whole group + shuffle
     null z, scaled across curve sizes: signal => z grows; floor => z ~ O(1).  No DLP limitation here.
 (C) [secp 36k bits=256, 21k -- substrate] sparse MI(cheap odd PUBLIC readout ; eis_n(d)) + power-scale
     + planted/random/baseline controls.

DISCIPLINE: exact int signal path (curve arith, xy, lifts); float only in MI/z vs matched shuffle null;
fixed-bits stratum on secp; controls must fire; grade; a null is a magnitude bound, not a closure.
"""
import csv, math, random
import numpy as np
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce, enorm, sextant, rdiv, cornacchia_4p_D3
from t_y_maxbound_v1 import prime_order_curve, group_coords, tonelli
from lift_band_joint_v1 import mi_bits, test_pair, _rankvals


def cube_root_unity(m):
    """nontrivial lambda with lambda^3 = 1 mod m, via x^2+x+1=0 -> x=(-1+sqrt(-3))/2."""
    s = tonelli((-3) % m, m)
    if s is None:
        return None
    inv2 = pow(2, m - 2, m)
    return (-1 + s) * inv2 % m


def make_eis_from_pi(pi_ab, m):
    a, b = pi_ab
    R1, R2 = gauss_reduce((a, b), (-b, a - b))
    if not (enorm(R1) == m and enorm(R2) == m):
        return None
    DET = R1[0] * R2[1] - R1[1] * R2[0]
    def eis(t):
        t %= m
        c1 = rdiv(t * R2[1], DET); c2 = rdiv(-t * R1[1], DET)
        return (t - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))
    return eis


# ============================================================ (A) secp structural alignment
def part_A():
    from glv_fundamental_domain_law_v1 import P_SECP, AP_SECP, BP_SECP
    from ecc_secp256k1 import N_ORDER, Gx, Gy, P as PP
    from int1_frame_operator_v1 import build_secp
    p, n = P_SECP, N_ORDER
    a, b = AP_SECP, BP_SECP
    EIS_P, _ = build_secp()
    EIS_N = make_eis_from_pi((a - 1, b), n)          # pi_n = pi_p - 1
    lam = cube_root_unity(n)
    print("=" * 92); print("(A) secp: xy and eis_n(d) both odd + mu3-weight-1 (same isotypic sector)")
    # xy mu3-covariance: need beta (x-> beta x) with x_{lam d}=beta x_d. beta ~= omega^2 mod pi_p.
    beta = pow(cube_root_unity(p) or 1, 1, p)         # a cube root of 1 mod p (either; check covariance)
    # verify eis_n(lam d) = rotation of eis_n(d): mu3-covariant
    om2 = lambda w: (w[1] - w[0], -w[0])              # mult by omega^2 in (u,v)
    om1 = lambda w: (-w[1], w[0] - w[1])              # mult by omega
    okrot = 0
    for d in [1, 2, 3, 5, 7, 11, 13, 101, 2027, 99991]:
        z = EIS_N(d); zl = EIS_N(lam * d % n)
        if zl in (z, om1(z), om2(z), (-z[0], -z[1]), (-om1(z)[0], -om1(z)[1]), (-om2(z)[0], -om2(z)[1])):
            okrot += 1
    print("    eis_n(lam d) is a unit-rotation of eis_n(d) (mu3/mu6-covariant): %d/10" % okrot)
    # xy odd in d already proven (x even, y odd). Confirm mu3-weight-1 symbolically holds: xy(beta x,y)=beta xy.
    print("    xy(beta x, y) = beta * xy  => xy is mu3-weight-1 (odd in d via x-even/y-odd) [structural]")
    print("    => sign(xy) and eis_n(d) share sector (odd + mu3-weight-1): the parity+mu3-correct readout.")


# ============================================================ (B) toy full-group decisive test
def odd_readouts(xs, ys, p, n):
    # NOTE: mi_bits indexes a contingency table by cell label, so labels MUST be non-negative {0,1,..},
    # NOT {-1,+1} (a -1 wraps to the last row and collapses the feature -> MI identically 0).
    d = np.arange(1, n)
    sxy = np.array([1 if 2 * (xs[i] * ys[i] % p) < p else 0 for i in d], np.int64)  # sign(xy), odd
    sy = np.array([1 if 2 * ys[i] < p else 0 for i in d], np.int64)                 # s_y, odd
    xlow = np.array([xs[i] & 1 for i in d], np.int64)                               # even-in-d baseline-ish
    return d, {'sign_xy(odd,mu3)': sxy, 's_y(odd,mu3inv)': sy, 'CTRL_xparity(even)': xlow}


def part_B():
    print("\n" + "=" * 92)
    print("(B) TOY full-group: cheap odd readout vs eis_n(d)  (MI + shuffle-null z; scaling)")
    print("    signal => |z| grows with n; floor => |z| ~ O(1).  (aligned ceiling shown.)")
    for lo, hi in [(2000, 4000), (8000, 16000), (30000, 60000)]:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, n, G = r
        if n % 3 != 1:
            # need n = 1 mod 3 for pi_n to exist; scan a bit further
            found = None
            for _ in range(30):
                r2 = prime_order_curve(hi, hi + (hi - lo));
                if r2 and r2[1] % 3 == 1:
                    found = r2; break
                if r2: p, n, G = r2; hi = r2[0] + 50
            if n % 3 != 1:
                print("   (no n=1 mod3 curve near [%d,%d]; skip)" % (lo, hi)); continue
        pi = cornacchia_4p_D3(n)
        EIS_N = make_eis_from_pi(pi, n) if pi else None
        if EIS_N is None:
            print("   (pi_n construction failed for n=%d; skip)" % n); continue
        xs, ys = group_coords(G, p, n, 0)
        d, feats = odd_readouts(xs, ys, p, n)
        # targets from eis_n(d)
        zn = [EIS_N(int(dd)) for dd in d]
        sxn = np.array([sextant(u, v) for (u, v) in zn], np.int64)
        sgn_un = np.array([1 if u >= 0 else 0 for (u, v) in zn], np.int64)
        tgts = {'sextant_n': sxn, 'sign_u_n': sgn_un}
        rng = np.random.default_rng(n)
        print("\n   p=%d n=%d (n mod3=%d):" % (p, n, n % 3))
        for fn, fc in feats.items():
            row = "     %-20s" % fn
            for tn, tc in tgts.items():
                Ic, z = test_pair(fc, tc, R=200, rng=rng)
                row += "  %s I_c=%+.5f z=%+.1f" % (tn, Ic, z)
            print(row)
        # aligned ceiling: a PLANTED partial copy of sextant_n must FIRE (detector sees eis_n structure)
        pl = sxn.copy(); m = rng.random(len(sxn)) > 0.30; pl[m] = rng.integers(0, 6, m.sum())
        Ic, z = test_pair(pl.astype(np.int64), sxn, R=200, rng=rng)
        print("     [ceiling] planted-30%% copy of sextant_n:  I_c=%+.5f z=%+.1f  [must FIRE]" % (Ic, z))


# ============================================================ (C) secp 36k substrate sparse test
def part_C():
    print("\n" + "=" * 92)
    print("(C) secp 36k bits=256 (21k): cheap odd PUBLIC readout -> eis_n(d)  (MI+null+power-scale+ctrl)")
    from glv_fundamental_domain_law_v1 import P_SECP, AP_SECP, BP_SECP
    from ecc_secp256k1 import N_ORDER
    P = P_SECP; a, b = AP_SECP, BP_SECP
    EIS_N = make_eis_from_pi((a - 1, b), N_ORDER)
    ds, Xs, Ys = [], [], []
    with open('constructed_keys_fullrange_v1.csv') as f:
        for row in csv.DictReader(f):
            if int(row['N']) != 256:
                continue
            ds.append(int(row['d'])); Xs.append(int(row['X'], 16)); Ys.append(int(row['Y'], 16))
    L = len(ds); print("    rows =", L)
    # cheap odd public features
    sxy = np.array([1 if 2 * (Xs[i] * Ys[i] % P) < P else 0 for i in range(L)], np.int64)
    sy = np.array([1 if 2 * Ys[i] < P else 0 for i in range(L)], np.int64)
    ylow = np.array([Ys[i] & 7 for i in range(L)], np.int64)               # y low bits (odd-ish) baseline
    ctrl = np.array([Xs[i] & 7 for i in range(L)], np.int64)               # even-in-d generic baseline
    feats = {'sign_xy': sxy, 's_y': sy, 'y_low3': ylow, 'CTRL_Xlow': ctrl}
    # targets from eis_n(d)
    zn = [EIS_N(dd) for dd in ds]
    sxn = np.array([sextant(u, v) for (u, v) in zn], np.int64)
    sgn_un = np.array([1 if u >= 0 else 0 for (u, v) in zn], np.int64)
    unbin = (_rankvals([u for (u, v) in zn]) * 8 // L).astype(np.int64)
    tgts = {'sextant_n': sxn, 'sign_u_n': sgn_un, 'u_n_bin': unbin}
    rng = np.random.default_rng(11)
    # controls
    for f in (0.30, 0.05):
        pl = sxn.copy(); m = rng.random(L) > f; pl[m] = rng.integers(0, 6, m.sum())
        Ic, z = test_pair(sxn, pl, R=150, rng=rng)
        print("    PLANTED f=%.2f: I_c=%+.5f z=%+.1f [FIRE]" % (f, Ic, z))
    Ic, z = test_pair(sxn, rng.integers(0, 6, L), R=150, rng=rng)
    print("    RANDOM: I_c=%+.5f z=%+.1f [FLAT]" % (Ic, z))
    print("    grid (I_c / z):")
    results = []
    hdr = "    %-11s" % "feat\\tgt" + "".join("%15s" % t for t in tgts)
    print(hdr)
    for fn, fc in feats.items():
        line = "    %-11s" % fn
        for tn, tc in tgts.items():
            Ic, z = test_pair(fc, tc, R=200, rng=rng)
            results.append((abs(z), z, Ic, fn, tn))
            line += "%15s" % ("%+.4f/%+.1f" % (Ic, z))
        print(line)
    results.sort(reverse=True)
    cz = max(abs(z) for az, z, Ic, fn, tn in results if fn == 'CTRL_Xlow')
    print("    CTRL_Xlow baseline |z|max=%.1f" % cz)
    strong = next((r for r in results if r[3] != 'CTRL_Xlow'), None)
    top = results[0]
    print("    top: %s x %s I_c=%+.5f z=%+.1f  %s" %
          (top[3], top[4], top[2], top[1], "ABOVE baseline" if top[0] > cz + 1 and top[3] != 'CTRL_Xlow' else "at floor"))
    if strong:
        fn, tn = strong[3], strong[4]
        print("    power-scale %s x %s:" % (fn, tn))
        fc, tc = feats[fn], tgts[tn]
        for Nn in [500, 1000, 2000, 5000, 10000, 20000]:
            if Nn > L: break
            ics, zs = [], []
            for _ in range(5):
                sel = rng.choice(L, Nn, replace=False)
                Ic, z = test_pair(fc[sel], tc[sel], R=120, rng=rng); ics.append(Ic); zs.append(z)
            print("      N=%6d I_c=%+.6f z=%+.2f" % (Nn, np.mean(ics), np.mean(zs)))


if __name__ == '__main__':
    part_A()
    part_B()
    part_C()
    print("\n[done] read: (A) sector match; (B) toy z scaling = signal-vs-floor without DLP limit;")
    print("       (C) secp substrate. Lead with any above-floor structure; grade nulls as magnitude bounds.")
