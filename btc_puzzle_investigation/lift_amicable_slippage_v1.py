#!/usr/bin/env python3
"""
lift_amicable_slippage_v1.py -- the AMICABLE-SLIPPAGE probe (the "not obviously linked" channel).

secp is an amicable pair: n = N(pi_n), pi_n = pi_p - 1.  The scalar ring Z/n = Z[w]/(pi_n) and the
field ring F_p = Z[w]/(pi_p) therefore have CM rhombi that NEARLY COINCIDE -- reduced-basis slippage is
exactly R1p-R1n=(0,1), R2p-R2n=(1,1) (verified), i.e. the two lattices differ by ONE unit per coord
(~2^-128 relative).  Two residual objects on the same key index d:
  * FIELD lift  eis_p(X_d) = reduce x([d]G) into the (pi_p) rhombus   -- PUBLIC (from X)
  * SCALAR lift eis_n(d)   = reduce the scalar d into the (pi_n) rhombus -- function of the secret d
ECDLP scrambles d -> X_d, so a-priori eis_p(X_d) _|_ eis_n(d).  BUT the near-coincidence of the two
rhombi is the candidate mechanism for a sub-noise interference.  If public eis_p(X_d) predicted
eis_n(d) at all, that WOULD be a leak (eis_n(d) constrains d).  Build it, test it, grade it.

WHY the 36k set, bits=256: eis_n(d) only does a NON-TRIVIAL reduction when d exceeds the rhombus edge
(~sqrt(n) ~ 2^128); small keys give eis_n(d)=(d,0) (vacuous).  The 36k bits=256 stratum (21k keys,
d~2^255) is deep in the reducing regime and well powered.  Real-82 keys are mostly too small.

DISCIPLINE: exact int signal path (both lifts, norms, sextants); float only in MI/corr/z stats vs a
matched shuffle null; fixed-bits stratum (no bit-length confound); planted + random + raw-X controls;
power-scaling; grade.  A null is a scoped fact, not a closure.
"""
import csv
import numpy as np
from glv_fundamental_domain_law_v1 import P_SECP, AP_SECP, BP_SECP
from ecc_secp256k1 import N_ORDER
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce, enorm, sextant, rdiv
from int1_frame_operator_v1 import build_secp
from lift_band_joint_v1 import mi_bits, test_pair, _rankvals

P, N = P_SECP, N_ORDER
EIS_P, EPS_P = build_secp()                       # field-side lift of X (public)

# ---- scalar-side lift eis_n : reduce d into the (pi_n) rhombus ----------------------------
def make_scalar_lift():
    a, b = AP_SECP, BP_SECP
    R1, R2 = gauss_reduce((a - 1, b), (-b, a - 1 - b))     # ideal (pi_n = pi_p - 1)
    assert enorm(R1) == N and enorm(R2) == N
    DET = R1[0] * R2[1] - R1[1] * R2[0]
    def eis_n(d):
        d %= N
        c1 = rdiv(d * R2[1], DET); c2 = rdiv(-d * R1[1], DET)  # reduce (d,0)
        return (d - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))
    return eis_n, R1, R2
EIS_N, R1n, R2n = make_scalar_lift()

def qcells(vals, q=8):
    r = _rankvals(vals); return (r * q // len(vals)).astype(np.int64)

def pearson_with_null(a, b, reps=200, seed=0):
    a = np.asarray(a, float); b = np.asarray(b, float)
    a = a - a.mean(); b = b - b.mean()
    rho = float(np.dot(a, b) / (np.linalg.norm(a) * np.linalg.norm(b) + 1e-18))
    rng = np.random.default_rng(seed); nulls = np.empty(reps)
    for i in range(reps):
        bs = rng.permutation(b)
        nulls[i] = np.dot(a, bs) / (np.linalg.norm(a) * np.linalg.norm(bs) + 1e-18)
    return rho, (rho - nulls.mean()) / (nulls.std() + 1e-12)

# ---- load 36k bits=256 stratum -----------------------------------------------------------
def load(path='constructed_keys_fullrange_v1.csv', bits=256):
    ds, Xs, Ys = [], [], []
    with open(path) as f:
        for row in csv.DictReader(f):
            if int(row['N']) != bits:
                continue
            ds.append(int(row['d'])); Xs.append(int(row['X'], 16)); Ys.append(int(row['Y'], 16))
    return ds, Xs, Ys

def main():
    print("=" * 92)
    print("AMICABLE-SLIPPAGE probe: field-lift eis_p(X)  vs  scalar-lift eis_n(d)   [36k, bits=256]")
    print("=" * 92)
    print("slippage R1p-R1n=(0,1) R2p-R2n=(1,1) [verified]; N(R1n)=N(R2n)=n [verified]")

    # sanity: eis_n trivial for small d, nontrivial for large d
    small = EIS_N(12345); big = EIS_N((N >> 2) + 7)
    print("sanity eis_n(12345)=%s (trivial=(d,0):%s);  eis_n(~n/4) reduces: |u|~2^%d" %
          (small, small == (12345, 0), max(1, big[0].bit_length())))

    ds, Xs, Ys = load()
    L = len(ds); print("stratum rows =", L)

    # ---- exact features (field, public) and targets (scalar, from d) ----
    up = np.empty(L); vp = np.empty(L); sp = np.empty(L); sxp = np.empty(L, np.int64); epp = np.empty(L, np.int64)
    un = np.empty(L); vn = np.empty(L); sn = np.empty(L); sxn = np.empty(L, np.int64)
    sxy = np.empty(L, np.int64)
    # slippage isolate: SAME value X reduced under BOTH lattices -> delta = eis_p(X)-eis_n(X) is purely
    # the (0,1)/(1,1) slippage effect (a public function of X).
    du = np.empty(L); dv = np.empty(L); dmag = np.empty(L)
    for i in range(L):
        zp = EIS_P(Xs[i]); up[i], vp[i] = zp; sp[i] = enorm(zp); sxp[i] = sextant(*zp); epp[i] = EPS_P(Xs[i])
        zn = EIS_N(ds[i]); un[i], vn[i] = zn; sn[i] = enorm(zn); sxn[i] = sextant(*zn)
        zpn = EIS_N(Xs[i])                                  # reduce the FIELD value X under (pi_n)
        du[i] = zp[0] - zpn[0]; dv[i] = zp[1] - zpn[1]; dmag[i] = enorm((int(du[i]), int(dv[i])))
        sxy[i] = 1 if 2 * (Xs[i] * Ys[i] % P) < P else 0

    rng = np.random.default_rng(2024)

    # ========================================================================================
    # A. DIRECT GEOMETRIC COUPLING  (do the two lifts co-vary, given the rhombi nearly coincide?)
    # ========================================================================================
    print("\n-- A. direct geometric coupling  (Pearson of field-lift vs scalar-lift; shuffle-null z) --")
    for nm, aa, bb in [('u_p~u_n', up, un), ('v_p~v_n', vp, vn), ('s_p~s_n', sp, sn),
                       ('u_p~v_n', up, vn), ('s_p~u_n', sp, un)]:
        rho, z = pearson_with_null(aa, bb, seed=int(rng.integers(1e9)))
        print("   %-9s  rho=%+.4f  z=%+.1f" % (nm, rho, z))
    print("   sextant_p x sextant_n (MI):")
    Ic, z = test_pair(sxp, sxn, R=200, rng=rng)
    print("      I_c=%+.5f bits  z=%+.1f" % (Ic, z))

    # ========================================================================================
    # B. LEAK FRAMING  (public field features -> scalar-lift target cells)  + controls
    # ========================================================================================
    print("\n-- B. leak framing: public eis_p(X) feature -> eis_n(d) target  (I_c bits / z) --")
    feats = {'sextant_p': sxp, 'flap_p': epp, 'sign_xy': sxy,
             's_p_bin': qcells(sp), 'u_p_sign': (up >= 0).astype(np.int64),
             'slip_du_sign': (du >= 0).astype(np.int64), 'slip_mag_bin': qcells(dmag),
             'CTRL_Xlow': np.array([x & 7 for x in Xs], np.int64)}
    tgts = {'sextant_n': sxn, 's_n_bin': qcells(sn),
            'u_n_sign': (un >= 0).astype(np.int64), 'u_n_bin': qcells(un)}
    # controls
    base = sxp
    for f in (0.30, 0.05):
        pl = base.copy(); m = rng.random(L) > f; pl[m] = rng.integers(0, 6, m.sum())
        Ic, z = test_pair(base, pl % 8, R=150, rng=rng)
        print("   PLANTED f=%.2f: I_c=%+.5f z=%+.1f [want FIRE]" % (f, Ic, z))
    Ic, z = test_pair(base, rng.integers(0, 8, L), R=150, rng=rng)
    print("   RANDOM:        I_c=%+.5f z=%+.1f [want FLAT]" % (Ic, z))
    print("   grid:")
    hdr = "   %-11s" % "feat\\tgt" + "".join("%14s" % t for t in tgts)
    print(hdr)
    results = []
    for fn, fc in feats.items():
        line = "   %-11s" % fn
        for tn, tc in tgts.items():
            Ic, z = test_pair(fc, tc, R=200, rng=rng)
            results.append((abs(z), z, Ic, fn, tn))
            line += "%14s" % ("%+.4f/%+.1f" % (Ic, z))
        print(line)
    results.sort(reverse=True)
    ctrl = max(abs(z) for az, z, Ic, fn, tn in results if fn == 'CTRL_Xlow')
    print("   CTRL_Xlow baseline |z|max = %.1f (lift feature must beat this)" % ctrl)
    top = results[0]
    print("   top cell: %s x %s  I_c=%+.5f z=%+.1f  %s" %
          (top[3], top[4], top[2], top[1], "ABOVE baseline" if top[0] > ctrl + 1 and top[3] != 'CTRL_Xlow' else "at floor"))

    # ---- power-scale the strongest non-control cell ----
    strong = next((r for r in results if r[3] != 'CTRL_Xlow'), None)
    if strong:
        fn, tn = strong[3], strong[4]
        print("\n-- power-scaling %s x %s (signal: I_c plateau + z~sqrt(N); noise: I_c~1/N flat) --" % (fn, tn))
        fc, tc = feats[fn], tgts[tn]
        for Nn in [500, 1000, 2000, 5000, 10000, 20000]:
            if Nn > L: break
            ics, zs = [], []
            for _ in range(5):
                sel = rng.choice(L, Nn, replace=False)
                Ic, z = test_pair(fc[sel], tc[sel], R=120, rng=rng); ics.append(Ic); zs.append(z)
            print("   N=%6d  I_c=%+.6f  z=%+.2f" % (Nn, np.mean(ics), np.mean(zs)))

    print("\n[done]  Read: A rho~0 & B grid at CTRL floor => two lifts independent (scoped null);")
    print("        any cell above baseline that power-ramps ~sqrt(N) => the amicable interference is real.")

if __name__ == '__main__':
    main()
