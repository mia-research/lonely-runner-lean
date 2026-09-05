#!/usr/bin/env python3
"""
theta_structure_scan_v1.py -- EXPLORATORY.  No verdict, no grade, no leakage claim.

THE OBJECT: is  a -> theta_a  ARITHMETICALLY STRUCTURED?
(record's ranked item 3'/4', SYNTHESIS_..._ADDENDUM_1_v1.md Sec 3.3 / Sec 4 -- never run.)

WHY IT IS NOT ALREADY ANSWERED.  The 120-degree law gives the eigenvalue configuration
{alpha, alpha*z3, -abar, -abar*z3bar}, alpha = sqrt(p) e^{i theta_a}, so

    V(a) = 2i sqrt(p) sin(theta_a + 60deg),      u(a) := V(a)/(2i sqrt p) = sin(theta_a+60)

theta_a is the ONE FREE angle; the relative angle is frozen. Every twist-orbit statistic
in the record measures theta_a THROUGH the forced sin(.+60) envelope -- moments of u,
the magnitude spectrum, the additive autocorrelation. Those are LINEAR/QUADRATIC in V and
are exactly the ones pinned by forced identities:
    sum_a V(a) Vbar(a+b) = n(n delta_b - 1)   [forced, curve-independent]
    V_2 = V_1^2 + 2p                          [forced BY the 120 config -- derived below]

DERIVATION (why extension fields are NOT needed, and why they would not help):
  p_1 = sum alpha_i = 2i sqrt(p) sin(theta+60)
  p_2 = sum alpha_i^2 = 2p cos(2 theta - 60) = 2p(2 sin^2(theta+60) - 1)
  => p_2 is a FUNCTION OF p_1 alone  => V_2 = V_1^2 + 2p is FORCED and carries ZERO
     information about theta beyond V_1.  The residual ambiguity theta+60 <-> 180-(theta+60)
     is invariant for both p_1 and p_2 and would need p_3 (i.e. E(F_{p^3}), O(p^3)).
  => we work with the FOLDED angle  th(a) = arcsin(u(a)) in [-90,90], which is exactly
     what V determines, and which is a NONLINEAR functional of V.

WHY NONLINEAR IS THE POINT.  The forced identities above constrain the first and second
moments of V.  They do NOT constrain arcsin(V) -- so ARRANGEMENT statistics of the angle
sequence are not forced, and have never been measured.

STATISTICS (all arrangement-sensitive; the null below is a pure arrangement null)
  A  ANGLE-INCREMENT AUTOCORRELATION: Delta(a) = th(a+1) - th(a); report the max |rho(l)|
     over lags l=1..L and the lag-1 value.
  B  MULTIPLICATIVITY: is u(a)u(b)/u(ab) concentrated?  (a character would give a constant.)
     Statistic = the resultant length |mean over sampled (a,b) of the unit phase of
     u(a)u(b)/u(ab)| -- 1 = perfectly multiplicative, ~1/sqrt(S) = generic.
  C  ANGLE SPACING: KS distance of the normalised spacings of sorted {th(a)} to the
     Sato-Tate-implied reference.  *** REPORTED AS DIAGNOSTIC ONLY *** -- spacings depend
     only on the MULTISET, and the arrangement null preserves the multiset exactly, so the
     null has ZERO power here by construction (same structural gap as the |V| tail).

NULL: the twist-orbit pipeline's own class permutation of the frequency-domain values,
which preserves the forced mu3 + odd symmetry AND the |V| multiset, and destroys ONLY the
arrangement in a.  Correct for A and B; powerless for C (stated, not hidden).

Exact int signal path; float only in the angle statistics, ranked against the null.
"""
import argparse, json, sys
import numpy as np
from sympy import primitive_root
from twist_orbit_spectrum_run_v1 import signal


def u_sequence(p, n, c):
    """u(a) = V(a)/(2i sqrt p) for a = 0..n-1.  V purely imaginary => u real."""
    V = np.fft.fft(c.astype(np.complex128))                    # noqa: float
    u = (V / (2j * np.sqrt(p))).real                           # noqa: float
    return u, V


def folded_angle(u):
    """th = arcsin(u), the angle V actually determines (see header derivation)."""
    return np.arcsin(np.clip(u, -1.0, 1.0))                    # noqa: float


def stat_A(th, L=12):
    """Angle-increment autocorrelation: max |rho(l)|, l=1..L, and rho(1)."""
    d = np.diff(th)
    d = d - d.mean()
    v = (d * d).sum()
    if v == 0:
        return 0.0, 0.0
    rr = [abs(float((d[:-l] * d[l:]).sum() / v)) for l in range(1, L + 1)]
    return max(rr), rr[0]


def stat_B(u, n, rng, S=4000):
    """Multiplicativity resultant: mean unit phase of u(a)u(b)/u(ab)."""
    a = rng.integers(1, n, size=S)
    b = rng.integers(1, n, size=S)
    ab = (a * b) % n
    ok = (ab != 0)
    a, b, ab = a[ok], b[ok], ab[ok]
    num = u[a] * u[b]
    den = u[ab]
    ok2 = np.abs(den) > 1e-12
    r = num[ok2] / den[ok2]
    ph = np.sign(r)                        # real object => phase in {+1,-1}
    return float(abs(ph.mean()))           # noqa: float


def class_perm_freq(V, n, rng):
    """The pipeline's null: permute the L mu6-class values of V, rebuild by the forced
    mu3-invariant + odd symmetry.  Preserves the |V| multiset exactly."""
    g = int(primitive_root(n))
    powg = np.empty(n - 1, dtype=np.int64)
    cur = 1
    for m in range(n - 1):
        powg[m] = cur
        cur = (cur * g) % n
    L = (n - 1) // 6
    rho = V[powg[:L]]
    rho = rho[rng.permutation(L)]
    m = np.arange(n - 1)
    sign = np.where((m // L) % 2 == 0, 1, -1)
    W = sign * rho[m % L]
    out = np.zeros(n, dtype=complex)                            # noqa: float
    out[powg] = W
    return out


def run(p, n_null, rng):
    s = signal(p, 7)
    if s is None:
        return None
    n, c, X, Y = s
    u, V = u_sequence(p, n, c)
    th = folded_angle(u)
    # ---- forced-structure controls (exact-ish) ------------------------------
    cap_ok = bool(np.max(np.abs(u)) <= 1.0 + 1e-9)              # |V| <= 2 sqrt p
    imag_ok = float(np.max(np.abs(V.real)))                     # noqa: float
    A_max, A_1 = stat_A(th)
    B = stat_B(u, n, rng)
    nA, nA1, nB = [], [], []
    for _ in range(n_null):
        Vn = class_perm_freq(V, n, rng)
        un = (Vn / (2j * np.sqrt(p))).real                      # noqa: float
        tn = folded_angle(un)
        a_, a1_ = stat_A(tn)
        nA.append(a_); nA1.append(a1_); nB.append(stat_B(un, n, rng))
    o = {"p": p, "n": int(n), "C_CAP": cap_ok, "C_IMAG_maxre": imag_ok,
         "A_max": A_max, "A_lag1": A_1,
         "A_null_mean": float(np.mean(nA)), "A_null_max": float(np.max(nA)),  # noqa: float
         "A_ge": int(sum(1 for v in nA if v >= A_max)),
         "A1_null_mean": float(np.mean(nA1)),                   # noqa: float
         "B": B, "B_null_mean": float(np.mean(nB)),             # noqa: float
         "B_null_max": float(np.max(nB)),                       # noqa: float
         "B_ge": int(sum(1 for v in nB if v >= B)), "nnull": n_null}
    print(f"p={p:5d} n={n:5d}  C_CAP={cap_ok} max|Re V|={imag_ok:.2e}")
    print(f"   A angle-increment autocorr : max|rho| {A_max:.4f} (lag1 {A_1:+.4f})   "
          f"null {o['A_null_mean']:.4f}/{o['A_null_max']:.4f}  ge={o['A_ge']}/{n_null}")
    print(f"   B multiplicativity resultant: {B:.4f}   "
          f"null {o['B_null_mean']:.4f}/{o['B_null_max']:.4f}  ge={o['B_ge']}/{n_null}")
    sys.stdout.flush()
    return o


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", type=int, nargs="+",
                    default=[823, 1303, 1831, 2251, 2731])
    ap.add_argument("--nnull", type=int, default=20)
    ap.add_argument("--seed", type=int, default=20260730)
    ap.add_argument("--out", default="theta_structure_scan_v1.json")
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    res = [r for r in (run(p, a.nnull, rng) for p in a.primes) if r]
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"\nwrote {a.out}")


if __name__ == "__main__":
    main()
