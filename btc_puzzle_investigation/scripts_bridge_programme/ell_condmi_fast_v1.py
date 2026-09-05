#!/usr/bin/env python3
"""PREREG_ell_ge5_conditional_MI_v1 -- numpy-accelerated conditional statistic + CALIBRATION.
Cross-checks the pure-Python machinery (M0, Mc+) then runs an empirical false-positive-rate
calibration of the two permutation nulls (they are exact by exchangeability; this confirms it).
Synthetic data only -- does NOT touch the frozen arms."""
import numpy as np

# ---------- statistics (vectorized; MI in nats, same as pure-Python) ----------
def _mi_from_joint(J):                       # J: 2D integer count matrix
    N = J.sum()
    if N == 0: return 0.0
    P = J / N
    pr = P.sum(1, keepdims=True); pc = P.sum(0, keepdims=True)
    with np.errstate(divide='ignore', invalid='ignore'):
        term = P * (np.log(P) - np.log(pr) - np.log(pc))
    return float(np.nansum(np.where(P > 0, term, 0.0)))

def Icond(j, k, w, ell):                     # stratified conditional MI I(j;k|w)
    code = (w * ell + j) * ell + k
    H = np.bincount(code, minlength=ell**3).reshape(ell, ell, ell)  # [w,j,k]
    N = len(j); tot = 0.0
    for wi in range(ell):
        Jw = H[wi]; Nw = Jw.sum()
        if Nw >= 2: tot += (Nw / N) * _mi_from_joint(Jw)
    return tot

def Tcond(j, k, w, ell):                      # max over choice-free alignments of I(j-b k ; w)
    best = 0.0
    for b in range(1, ell):
        d = (j - b * k) % ell
        H = np.bincount(d * ell + w, minlength=ell * ell).reshape(ell, ell)
        v = _mi_from_joint(H)
        if v > best: best = v
    return best

def MI(j, k, ell):
    H = np.bincount(j * ell + k, minlength=ell * ell).reshape(ell, ell)
    return _mi_from_joint(H)

# ---------- nulls ----------
def perm_Icond(j, k, w, ell, rng, sh):        # within-stratum shuffle of k
    obs = Icond(j, k, w, ell)
    groups = [np.where(w == wi)[0] for wi in range(ell)]
    ge = 0
    for _ in range(sh):
        kk = k.copy()
        for g in groups:
            kk[g] = kk[g][rng.permutation(len(g))]
        if Icond(j, kk, w, ell) >= obs - 1e-12: ge += 1
    return obs, (ge + 1) / (sh + 1)

def perm_Tcond(j, k, w, ell, rng, sh):        # shuffle w-labels
    obs = Tcond(j, k, w, ell); ge = 0
    for _ in range(sh):
        ww = w[rng.permutation(len(w))]
        if Tcond(j, k, ww, ell) >= obs - 1e-12: ge += 1
    return obs, (ge + 1) / (sh + 1)

def perm_MI(j, k, ell, rng, sh):
    obs = MI(j, k, ell); ge = 0
    for _ in range(sh):
        kk = k[rng.permutation(len(k))]
        if MI(j, kk, ell) >= obs - 1e-12: ge += 1
    return obs, (ge + 1) / (sh + 1)

if __name__ == "__main__":
    rng = np.random.default_rng(0)
    # ---- cross-check M0 + Mc+ against the pure-Python machinery ----
    print("=== M0 (numpy): choice-free under unit relabelings ===")
    ell = 7; N = 3000
    w = rng.integers(0, ell, N); k = rng.integers(0, ell, N)
    j = (k + w + rng.integers(0, 2, N)) % ell
    i0 = Icond(j, k, w, ell); t0 = Tcond(j, k, w, ell); oki = okt = True
    for a, c in ((2, 3), (3, 5), (6, 4)):
        oki &= abs(Icond((a*j) % ell, (c*k) % ell, w, ell) - i0) < 1e-12
        okt &= abs(Tcond((a*j) % ell, (c*k) % ell, w, ell) - t0) < 1e-12
    print(f"  Icond choice-free {oki}  Tcond choice-free {okt}")

    print("\n=== Mc+ (numpy): j=(k+w) marginal-blind, conditional-visible ===")
    print(f"  {'ell':>3} {'marg MI p':>10} {'Icond p':>9} {'Tcond p':>9}")
    for ell in (5, 7, 11, 13):
        rng = np.random.default_rng(100 + ell); N = 6000
        w = rng.integers(0, ell, N); k = rng.integers(0, ell, N); j = (k + w) % ell
        pm = perm_MI(j, k, ell, rng, 3000)[1]
        pi = perm_Icond(j, k, w, ell, rng, 3000)[1]
        pt = perm_Tcond(j, k, w, ell, rng, 3000)[1]
        print(f"  {ell:>3} {pm:>10.4f} {pi:>9.4f} {pt:>9.4f}")

    # ---- CALIBRATION: empirical FPR of both nulls under the synthetic global null ----
    print("\n=== CALIBRATION: FPR under H0 (j,k,w indep uniform), N=8000, R draws, sh=2000 ===")
    print("    permutation tests are exact by exchangeability => FPR should track alpha")
    print(f"  {'ell':>3} {'R':>4} {'Icond p<.05':>11} {'p<.01':>7} {'p<.00625':>9} | {'Tcond p<.05':>11} {'p<.01':>7} {'p<.00625':>9}")
    for ell in (5, 13):
        R = 200; N = 8000; sh = 2000
        rng = np.random.default_rng(9000 + ell)
        pi_list = []; pt_list = []
        for _ in range(R):
            w = rng.integers(0, ell, N); k = rng.integers(0, ell, N); j = rng.integers(0, ell, N)
            pi_list.append(perm_Icond(j, k, w, ell, rng, sh)[1])
            pt_list.append(perm_Tcond(j, k, w, ell, rng, sh)[1])
        pi = np.array(pi_list); pt = np.array(pt_list)
        f = lambda a, t: (a < t).mean()
        print(f"  {ell:>3} {R:>4} {f(pi,.05):>11.3f} {f(pi,.01):>7.3f} {f(pi,.00625):>9.3f} | "
              f"{f(pt,.05):>11.3f} {f(pt,.01):>7.3f} {f(pt,.00625):>9.3f}")
