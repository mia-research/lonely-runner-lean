#!/usr/bin/env python3
"""characterize_n1_v1.py -- characterize the STRUCTURE behind g=2 (no verdict, per anomaly-drill).
EXACT/MODULAR only (no float).  Tests the [REV §4b] omega-descent claim L*(a) = L*(lambda a)
and the internal shape, to decide whether §4b can be the uniformity lever for order-pinning.
"""
import audit_n1_vsign_v2_core as core
import run_n1_120deg_v1 as R

def Lstar_modl(p, n, h1, h2, a, l, r):
    inv2 = pow(2, l-2, l); ra = pow(r, a % n, l); rp = 1; V1 = 0; V2 = 0
    for d in range(n):
        if h1[d]: V1 = (V1 + h1[d]*rp) % l
        if h2[d]: V2 = (V2 + h2[d]*rp) % l
        rp = rp*ra % l
    leg = 1 if p % 4 == 1 else -1
    e1 = (-V1) % l; e2 = (V1*V1 + V2)*inv2 % l; e3 = (leg*p*e1) % l; e4 = (p*p) % l
    return [e4, (-e3) % l, e2, (-e1) % l, 1], e1, V1

def _eval(L, x, l):
    v = 0
    for c in reversed(L):        # Horner, low->high stored so reverse
        v = (v*x + c) % l
    return v

def roots_modl(L, l):
    return [x for x in range(l) if _eval(L, x, l) == 0]

def characterize(p, ncells=4):
    n = core.curve_order(p); assert core.is_prime(n), (p, n)
    dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
    reps = R.mu6_reps(n)
    l = R.ell_primes(n, 1)[0]
    r = R.primitive_root_of_order(n, l); w = R.primitive_root_of_order(3, l)
    lam = R.cube_root_of_unity(n)               # order-3 element of (Z/n)*  (= omega's action)
    assert pow(lam, 3, n) == 1 and lam != 1
    descent_ok = True; ratio_count = []
    sig_lam_perm = []
    for a in reps[:ncells]:
        La, e1a, V1a = Lstar_modl(p, n, h1, h2, a, l, r)
        Lla, _, _ = Lstar_modl(p, n, h1, h2, (a*lam) % n, l, r)
        if La != Lla: descent_ok = False
        rts = roots_modl(La, l)
        # count roots alpha with w*alpha also a root (= g, the between/within zeta3 links)
        cnt = sum(1 for al in rts if (w*al) % l in rts)
        ratio_count.append(cnt)
        # does the FROBENIUS/Galois sigma_lam: zeta_n -> zeta_n^lam permute the 4 eigenvalues?
        # sigma_lam(L*(a)) has coeffs = L*(a) with r -> r^lam, i.e. = L*(lam^{-1} a) reindexed.
        # We test the multiset invariance already (descent). Record roots for inspection.
        sig_lam_perm.append(sorted(rts))
    print(f"p={p:>4} n={n:>5} lam={lam:>4} (ord3) | omega-descent L*(a)==L*(lam a): {descent_ok} "
          f"| #roots a with w*a in roots: {ratio_count}  (=g per cell)")
    return descent_ok, ratio_count

if __name__ == "__main__":
    for p in (13, 43, 67, 127, 823, 1051):
        characterize(p)
