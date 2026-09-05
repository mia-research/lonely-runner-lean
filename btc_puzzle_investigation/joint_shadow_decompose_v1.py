#!/usr/bin/env python3
"""
joint_shadow_decompose_v1.py -- CHARACTERIZE the joint (x,y) shadow (the v16 "0.93").

This is a measurement, not an interpretation. Two jobs:
  (A) pin the number under a normalization that a PERFECT leak forces to 1.000
      (v16 used |Corr|/sqrt(n) and a coefficient-COUNT proxy for ||F||; neither reads
       1.0 for a perfect leak, so the 0.93 was never on an honest scale);
  (B) DECOMPOSE the aligned joint readout by mu6-isotype PARITY (even-in-d = x-carried,
      odd-in-d = y-carried) and report, as numbers, exactly how the x part and the y
      part each contribute to the alignment with the leaking character e_n(a0 d).

------------------------------------------------------------------ PRE-REGISTRATION
OBJECT   E: y^2 = x^3 + 7 over F_p, prime order n (enumerable d). a0 = 1 fixed.
         U(a0,b,c) = sum_{d=1..n-1} e_n(a0 d) e_p(b x_d + c y_d).
         Aligned readout (frequency support S):  Fhat(b,c) = conj(U)/|U| on S, else 0.
         Point-space F(P) = sum_{b,c in S} Fhat(b,c) e_p(-b x - c y)   [ifft2 on the grid].

STATISTIC (honest correlation coefficient, Cauchy-Schwarz bounded by 1):
         rho2 = |Corr| / ||F||_2 ,  Corr = (1/(n-1)) sum_d F(P_d) e_n(a0 d),
                ||F||_2 = sqrt( mean_d |F(P_d)|^2 ).      (c = e_n(a0.) is unit-norm.)
         Also reported: rho_inf = |Corr|/||F||_inf (TRUE point-space sup-norm), and
         M1 = |Corr|/sqrt(n) (the v16-faithful number, for comparison only).

SUPPORTS  S_joint = all (b,c) != (0,0);  S_sep = {(b,0)} (x-only).

PARITY DECOMPOSITION of the joint readout (same F, same norm):
         F_even(d) = (F(P_d)+F(P_{-d}))/2 ,  F_odd(d) = (F(P_d)-F(P_{-d}))/2 ,
         using P_{-d} = (x_d, p - y_d) [x even in d, y odd in d].
         Corr = Corr_even + Corr_odd (even _|_ odd). Report both /||F||_2.
         CLAIM UNDER TEST (v16): separable ~ Corr_even only; y supplies Corr_odd.

CONTROLS (must fire; a wrong normalization cannot pass C1):
   C1 planted perfect leak  F := e_n(a0 d)          -> rho2 == 1.000, rho_inf == 1.000
   C2 random point-function F := iid unit phases     -> rho2 ~ sqrt(1/(n-1)) (floor)
   C3 isotype orthogonality  <F_even, c_odd> == 0    and  <F_odd, c_even> == 0  (exact)
POWER (calibration)  graded plant F = a e_n(a0 d) + b*(random), sweep mix -> rho2 tracks it.
FALSIFICATION  if S_sep rho2 is NOT ~0.34 or S_joint NOT ~0.93 under an honest (C1-passing)
   norm, the v16 headline number is re-opened as a normalization artifact.
SCOPE  enumerable model primes p in {163..~500}; secp (2^256) is not enumerable. No verdict
   about exploitability is produced here -- only the object's structure.
------------------------------------------------------------------------------------
FLOAT CARVE-OUT: analytic-size character sums; curve/group arithmetic is exact int
(t_y_maxbound_v1). numpy float only in the |U| magnitudes / FFT (no key in the path).
"""
import argparse
import math
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords

EPS = 1e-9


def glv_beta(p):
    e = (p - 1) // 3
    g = 2
    while pow(g, e, p) == 1:
        g += 1
    return pow(g, e, p)


def build_U(xs, ys, p, n, a0):
    """U[b,c] = sum_{d=1..n-1} e_n(a0 d) e_p(b x_d + c y_d), as a p x p complex array."""
    w = np.exp(2j * np.pi * a0 * np.arange(n) / n)
    w[0] = 0.0
    H = np.zeros((p, p), dtype=complex)
    xi = np.array(xs, dtype=np.int64)
    yi = np.array(ys, dtype=np.int64)
    np.add.at(H, (xi[1:], yi[1:]), w[1:])
    return np.fft.fft2(H)              # H[x,y] -> U[b,c]


def full_report(U, xs, ys, p, n, w1):
    """Compute joint & separable rho, and the parity split of the joint readout.

    Aligned coefficient is Fh = U/|U| (not conj): with numpy's FFT sign conventions
    the point-space pairing already contributes conj(U), so Fh*conj(U) = |U| requires
    Fh = U/|U|.  Verified: this makes the joint readout's |Corr| = (1/(n-1)) sum|U|.
    """
    xi = np.array(xs[1:], dtype=np.int64)
    yi = np.array(ys[1:], dtype=np.int64)
    ymir = (p - yi) % p               # y-coordinate of -d

    def grid_of(mask):
        m = mask & (np.abs(U) > EPS)
        Fh = np.zeros_like(U); Fh[m] = U[m] / np.abs(U[m]); Fh[0, 0] = 0.0
        return np.fft.ifft2(Fh) * (p * p)

    out = {}
    for name, mask in (("separable", sep_mask(p)), ("joint", joint_mask(p))):
        Fg = grid_of(mask)
        Fd = Fg[xi, yi]
        Fdm = Fg[xi, ymir]                       # F at P_{-d}
        Fe = 0.5 * (Fd + Fdm)                    # even-in-d part
        Fo = 0.5 * (Fd - Fdm)                    # odd-in-d part
        corr = np.mean(Fd * np.conj(w1))
        corr_e = np.mean(Fe * np.conj(w1))
        corr_o = np.mean(Fo * np.conj(w1))
        l2 = math.sqrt(float(np.mean(np.abs(Fd) ** 2))) or 1e-18
        linf = float(np.max(np.abs(Fd))) or 1e-18
        # cross-orthogonality checks (C3): <F_even, c_odd> and <F_odd, c_even>
        c_even = np.cos(2 * np.pi * np.arange(1, n) * 1 / n)   # even part of e_n(a0 d)
        c_odd = 1j * np.sin(2 * np.pi * np.arange(1, n) * 1 / n)
        xort = abs(np.mean(Fe * np.conj(c_odd))) + abs(np.mean(Fo * np.conj(c_even)))
        out[name] = dict(rho2=abs(corr) / l2, rho_inf=abs(corr) / linf,
                         M1=abs(corr) / math.sqrt(n),
                         corr=abs(corr), corr_e=abs(corr_e), corr_o=abs(corr_o),
                         even_frac=abs(corr_e) / l2, odd_frac=abs(corr_o) / l2,
                         xort=xort)
    return out


def recon_fidelity(xs, ys, p, n, g, mask):
    """Phase-only reconstruction fidelity for an ARBITRARY target g(d), on frequency support mask.
    Build g's (b,c)-spectrum V over the point set, keep phases only (Fh=V/|V|) on mask, reconstruct
    in point space, correlate with g. Tests whether a fidelity is SPECIFIC to the leaking character
    or a GENERIC property of phase-only reconstruction on this point set (char vs random target).
    (Replaces the asserted 'F parallel c because |U| flat' mechanism with a measurement.)"""
    xi = np.array(xs[1:], dtype=np.int64); yi = np.array(ys[1:], dtype=np.int64)
    H = np.zeros((p, p), dtype=complex)
    np.add.at(H, (xi, yi), g)
    V = np.fft.fft2(H)
    m = mask & (np.abs(V) > EPS)
    Fh = np.zeros_like(V); Fh[m] = V[m] / np.abs(V[m]); Fh[0, 0] = 0.0
    Fg = np.fft.ifft2(Fh) * (p * p)
    Fd = Fg[xi, yi]
    corr = np.mean(Fd * np.conj(g))
    l2 = math.sqrt(float(np.mean(np.abs(Fd) ** 2))) or 1e-18
    gn = math.sqrt(float(np.mean(np.abs(g) ** 2))) or 1e-18
    return abs(corr) / (l2 * gn)


def flatness(U):
    """mean(|U|)^2 / mean(|U|^2) over (b,c)!=(0,0); 1.0 == perfectly flat magnitude spectrum."""
    a = np.abs(U).astype(float).copy(); a[0, 0] = np.nan
    mean = np.nanmean(a); msq = np.nanmean(a ** 2)
    return mean * mean / msq, mean, float(np.nanmax(a))


def joint_mask(p):
    m = np.ones((p, p), dtype=bool); m[0, 0] = False; return m


def sep_mask(p):
    m = np.zeros((p, p), dtype=bool); m[:, 0] = True; m[0, 0] = False; return m


def controls(xs, ys, p, n, w1):
    xi = np.array(xs[1:], dtype=np.int64)
    # C1 planted perfect leak: F_d = e_n(a0 d)
    Fp = w1.copy()
    corr = np.mean(Fp * np.conj(w1)); l2 = math.sqrt(float(np.mean(np.abs(Fp) ** 2)))
    linf = float(np.max(np.abs(Fp)))
    c1 = (abs(corr) / l2, abs(corr) / linf)
    # C2 random unit-phase point function
    rng = np.random.default_rng(p)
    Fr = np.exp(2j * np.pi * rng.random(n - 1))
    corr = np.mean(Fr * np.conj(w1)); l2 = math.sqrt(float(np.mean(np.abs(Fr) ** 2)))
    c2 = abs(corr) / l2
    floor = math.sqrt(1.0 / (n - 1))
    # POWER: graded plant
    grade = []
    for alpha in (1.0, 0.7, 0.5, 0.3, 0.15, 0.0):
        Fg = alpha * w1 + (1 - alpha) * np.exp(2j * np.pi * rng.random(n - 1))
        corr = np.mean(Fg * np.conj(w1)); l2 = math.sqrt(float(np.mean(np.abs(Fg) ** 2)))
        grade.append((alpha, abs(corr) / l2))
    return c1, c2, floor, grade


def run(p_lo, p_hi, smoke=False):
    r = prime_order_curve(p_lo, p_hi)
    if not r:
        return None
    p, n, G = r
    xs, ys = group_coords(G, p, n, 0)
    w1 = np.exp(2j * np.pi * 1 * np.arange(1, n) / n)   # e_n(a0=1 * d), d=1..n-1
    print(f"\n=== p={p}  n={n}  beta={glv_beta(p)} ===")
    c1, c2, floor, grade = controls(xs, ys, p, n, w1)
    print(f"  C1 planted perfect leak : rho2={c1[0]:.4f}  rho_inf={c1[1]:.4f}   (must be 1.0000)")
    print(f"  C2 random point-fn      : rho2={c2:.4f}   floor~{floor:.4f}")
    print(f"  POWER graded plant rho2 : " + "  ".join(f"a={a:.2f}:{v:.3f}" for a, v in grade))
    U = build_U(xs, ys, p, n, a0=1)
    # DECIDABLE CONTROL for the "joint rho2~1 is forced" claim: is high reconstruction
    # fidelity specific to the character, or generic to any target on this point set?
    rng2 = np.random.default_rng(p + 1)
    g_rand = np.exp(2j * np.pi * rng2.random(n - 1))
    jm, sm = joint_mask(p), sep_mask(p)
    jc = recon_fidelity(xs, ys, p, n, w1, jm); jr = recon_fidelity(xs, ys, p, n, g_rand, jm)
    sc = recon_fidelity(xs, ys, p, n, w1, sm); sr = recon_fidelity(xs, ys, p, n, g_rand, sm)
    fl, umean, umax = flatness(U)
    print(f"  RECON-FIDELITY (phase-only, char vs RANDOM target -- is a fidelity d-specific?):")
    print(f"      joint  : char={jc:.4f}  random={jr:.4f}   {'GENERIC' if abs(jc-jr)<0.03 else 'CHAR-SPECIFIC'}")
    print(f"      x-only : char={sc:.4f}  random={sr:.4f}   {'GENERIC' if abs(sc-sr)<0.03 else 'CHAR-SPECIFIC'}")
    print(f"  |U(a0,b,c)| flatness={fl:.3f} (1=flat)  mean={umean:.2f}(~sqrt n={math.sqrt(n):.2f})"
          f"  max={umax:.2f}(={umax/math.sqrt(p):.2f}sqrt p)")
    rep = full_report(U, xs, ys, p, n, w1)
    for name in ("separable", "joint"):
        d = rep[name]
        print(f"  [{name:9s}] rho2={d['rho2']:.4f}  rho_inf={d['rho_inf']:.4f}  "
              f"M1(v16)={d['M1']:.4f}   |Corr|={d['corr']:.4f}")
        print(f"              parity split: even(x)={d['even_frac']:.4f}  odd(y)={d['odd_frac']:.4f}"
              f"   C3 cross-orth={d['xort']:.2e}")
    j, s = rep["joint"], rep["separable"]
    print(f"  --> joint/separable rho2 ratio = {j['rho2']/max(s['rho2'],1e-9):.2f}x    "
          f"odd-lift = {j['odd_frac']:.3f} (the y surplus)")
    return p, n, rep


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--smoke", action="store_true")
    a = ap.parse_args()
    print("=" * 82)
    print("JOINT (x,y) SHADOW -- characterization & mu6-parity decomposition of the v16 0.93")
    print("=" * 82)
    if a.smoke:
        run(150, 250, smoke=True)
        return
    for lo, hi in [(150, 250), (250, 400), (400, 550), (550, 750)]:
        run(lo, hi)
    print("\n[done]")


if __name__ == "__main__":
    main()
