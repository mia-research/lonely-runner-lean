#!/usr/bin/env python3
"""
flap_grouplaw_transition_v1.py -- execute PREREG_flap_grouplaw_transition_v1.md.
Does the GROUP LAW (doubling) induce dependence in the mu6-invariant flap class ε? Exact int signal path.

ARM 0 (GATE): validate the ε classifier on secp -- mu6-invariance ZERO exceptions + 1/4 density.
T1 (PRIMARY): 2x2 table (ε(P), ε(2P)) on n uniform points; matched null = hypergeometric (fixed margins,
              = Fisher's exact conditional null); decision = two-sided rank p vs B draws. FIRES iff p<=1/120.
PC-max: map P->phi(P) (ε(βX)=ε(X) forced) -> diagonal table -> must fire.  PC-alpha: tunable power calib.
Classifier: ε(X)=1 iff |cent(aX)-cent(ρ·aX)|>p/2, a from the CM reduced basis, ρ primitive 6th root.
"""
import sys, random
import numpy as np
from avenue5_only import p, R1, R2, DET, eis_p

BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
RHO = (BETA + 1) % p
assert pow(BETA, 3, p) == 1 and (RHO * RHO - RHO + 1) % p == 0
ALPHA = (1, 120)


def extract_a():
    for X in range(1, 80):
        ar, br = eis_p(X)
        num = p * (ar * R2[1] - br * R2[0])
        assert num % DET == 0
        m = (num // DET) % p
        if m != 0:
            a = m * pow(X, p - 2, p) % p
            # verify cent(aX)=p*u(X) on a few
            for Y in range(1, 30):
                ar2, br2 = eis_p(Y)
                assert cent(a * Y % p) == (p * (ar2 * R2[1] - br2 * R2[0])) // DET
            return a
    raise RuntimeError("a not extracted")


def cent(u):
    u %= p
    return u - p if u > (p - 1) // 2 else u

A = None  # set after cent defined


def eps(X):
    s = A * X % p
    return 1 if 2 * abs(cent(s) - cent(RHO * s % p)) > p else 0


def batch_inv(vals):
    if not vals:
        return []
    pref = [1] * (len(vals) + 1)
    for i, v in enumerate(vals):
        pref[i + 1] = pref[i] * v % p
    inv = pow(pref[-1], p - 2, p)
    out = [0] * len(vals)
    for i in range(len(vals) - 1, -1, -1):
        out[i] = inv * pref[i] % p
        inv = inv * vals[i] % p
    return out


def x_double_batch(Xs):
    """x(2P) for y^2=x^3+7: (X^4 - 56 X) / (4(X^3+7)) mod p. Batch inverse. None if 2-torsion."""
    dens = []
    for X in Xs:
        d = 4 * ((X * X % p * X + 7) % p) % p
        dens.append(d if d != 0 else 1)
    invs = batch_inv(dens)
    out = []
    for X, inv, d0 in zip(Xs, invs, (4 * ((X * X % p * X + 7) % p) % p for X in Xs)):
        if d0 == 0:
            out.append(None)
        else:
            out.append((pow(X, 4, p) - 56 * X) % p * inv % p)
    return out


def valid_abscissas(n, seed):
    """n uniform X with X^3+7 a QR (on-curve), skipping 3-torsion (x(2P)=X)."""
    rng = random.Random(seed); out = []
    while len(out) < n:
        X = rng.randrange(1, p)
        if pow((X * X % p * X + 7) % p, (p - 1) // 2, p) == 1:
            out.append(X)
    return out


def table2x2(eA, eB):
    """counts (CC,CF,FC,FF) for paired 0/1 label lists."""
    cc = cf = fc = ff = 0
    for a, b in zip(eA, eB):
        if a:
            ff += b; fc += 1 - b
        else:
            cf += b; cc += 1 - b
    return cc, cf, fc, ff


def hyper_pval_twosided(cc, cf, fc, ff, B, seed):
    """matched independence null = Hypergeometric(n, row_F, col_F) for n_FF; two-sided rank p.
    EXACT integer two-sided distance: compare n*draw vs rowF*colF (= n*mean), no float."""
    n = cc + cf + fc + ff
    rowF = fc + ff          # flaps in domain
    colF = cf + ff          # flaps in image
    target = rowF * colF    # = n * E[n_FF|indep]
    obs_d = abs(n * ff - target)
    rs = np.random.default_rng(seed)
    draws = rs.hypergeometric(rowF, n - rowF, colF, size=B)
    ge = sum(1 for d in draws.tolist() if abs(n * d - target) >= obs_d)
    return (1 + ge, B + 1), target, n


def fires(pv):
    return pv[0] * ALPHA[1] <= ALPHA[0] * pv[1]


def main():
    global A
    A = extract_a()
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    B = int(sys.argv[2]) if len(sys.argv) > 2 else 9999
    print(f"# flap group-law doubling test | n={n} B={B} | a bits={A.bit_length()} rho ok")

    # ---- ARM 0 gate ----
    ng = 1 << 16
    gate = valid_abscissas(ng, 20260721)
    b2 = BETA * BETA % p
    exc = 0; nf = 0
    for X in gate:
        e = eps(X); nf += e
        if not (eps(BETA * X % p) == e == eps(b2 * X % p) == eps((p - X) % p)):
            exc += 1
    from math import isqrt
    dens_ok = abs(4 * nf - ng) <= 6 * isqrt(3 * ng)
    print(f"# ARM0 gate: mu6 exceptions={exc}/{ng} (need 0); flap density={nf}/{ng}"
          f" band_ok={dens_ok} -> {'PASS' if exc==0 and dens_ok else 'ABORT'}")
    if exc != 0 or not dens_ok:
        print("ARM0 FAILED -> no verdict"); return

    # ---- sample points, guard 3-torsion ----
    Xs = valid_abscissas(n, 424242)
    X2 = x_double_batch(Xs)
    dom = []; img = []
    for X, x2 in zip(Xs, X2):
        if x2 is None or x2 == X:      # skip 2-torsion / 3-torsion (x(2P)=X)
            continue
        dom.append(eps(X)); img.append(eps(x2))

    # ---- T1 primary ----
    cc, cf, fc, ff = table2x2(dom, img)
    nn = cc + cf + fc + ff
    pv, target, _ = hyper_pval_twosided(cc, cf, fc, ff, B, 999)
    pFF5 = ff * 100000 // (fc + ff) if (fc + ff) else 0    # P(F|F) x1e5, integer
    eFF = target // nn                                     # E[n_FF|indep], integer
    print(f"\n=== T1 doubling (PRIMARY) n={nn} ===")
    print(f"  2x2 [CC={cc} CF={cf} FC={fc} FF={ff}]  P(F|F)={pFF5}/1e5 (marginal 25000/1e5)")
    print(f"  n_FF={ff}  E[n_FF|indep]~={eFF}  p_MC(two-sided)={pv[0]}/{pv[1]}"
          f"  -> {'FIRES' if fires(pv) else 'null'}")

    # ---- PC-max: map X -> beta*X (eps forced equal) ----
    img_pc = [eps(BETA * X % p) for X in Xs[:nn]]
    dom_pc = [eps(X) for X in Xs[:nn]]
    cc2, cf2, fc2, ff2 = table2x2(dom_pc, img_pc)
    pv2, _, _ = hyper_pval_twosided(cc2, cf2, fc2, ff2, B, 555)
    print(f"  PC-max (X->betaX, forced diagonal): [CF={cf2} FC={fc2}] (expect 0,0) "
          f"p={pv2[0]}/{pv2[1]} -> {'FIRES' if fires(pv2) else 'FAIL'}")

    # ---- PC-alpha: inject fraction alpha of forced-equal pairs into independence background ----
    print("  PC-alpha power calibration (inject alpha*n forced-equal pairs):")
    base_dom = dom[:]; base_img = img[:]
    for k in (1, 3, 6, 9):
        m = nn >> k
        d2 = base_dom[:]; i2 = base_img[:]
        for t in range(m):          # force first m image labels equal to domain (planted dependence)
            i2[t] = d2[t]
        c = table2x2(d2, i2)
        pvk, _, _ = hyper_pval_twosided(*c, B, 100 + k)
        print(f"    alpha=1/2^{k} (m={m}): FF={c[3]} p={pvk[0]}/{pvk[1]}"
              f" -> {'FIRES' if fires(pvk) else 'null'}")

    print(f"\n# primary = T1 @ n={nn}. alpha*=1/120. (ε classifier ARM0-validated on secp.)")


Xs_none = object()

if __name__ == "__main__":
    main()
