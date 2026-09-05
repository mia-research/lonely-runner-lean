#!/usr/bin/env python3
"""
n1_phase_cap_v2_controls.py — the two MUST-FIRE controls of PREREG_n1_phase_cap_v2.md
section 3.4.  If either fails, the null is uninformative and NO verdict may be issued.

P-CEIL (positive / ceiling witness).  The admissible target eps_O = sign(s_O(1)),
  s_O(a) = sum_{j=0..2} sin(2 pi a lambda^j d_O / n).  Its |V(1)| is computable from
  n ALONE before any curve readout: |V(1)| = 2 sum_O |s_O(1)|.
  PASS: measured |V(1)|/sqrt(p) equals the precomputed value to 1e-10 relative,
        AND S > 2.  This is what v1 had no way to show (D3): it proves the statistic
        CAN report S > 2 on an admissible +-1 target of the same shape as the readout.

P-FLOOR (negative / floor witness).  h = chi_n, the Legendre symbol mod n.  Its DFT is
  a Gauss sum, so |V(a)| = sqrt(n) for EVERY a != 0 and S lands EXACTLY on the Parseval
  floor sqrt(n/p).  PASS: relative deviation <= 1e-10.  This proves the statistic can
  also reach the floor, so it is not biased upward.

Together the two pin the realizable range [sqrt(n/p), ~0.318 sqrt(p)] with BOTH
endpoints attained by explicit named targets -- so no outcome is a bare magnitude.
"""
import numpy as np
from sympy.ntheory.residue_ntheory import nthroot_mod
from n1_phase_cap_v2_run import load_holdout, mu6_structure


def p_ceil(p, n):
    lam = [int(z) for z in nthroot_mod(1, 3, n, all_roots=True) if z != 1][0]
    idx, sgn, M = mu6_structure(n, lam)
    d = np.arange(1, n, dtype=np.int64)
    reps = np.zeros(M, dtype=np.int64)
    reps[idx] = np.where(sgn > 0, d, n - d)          # the "+" member of each orbit
    J = np.array([pow(lam, j, n) for j in range(3)], dtype=np.int64)
    ang = 2 * np.pi * ((reps[:, None] * J[None, :]) % n) / n
    s1 = np.sin(ang).sum(1)
    pred = 2 * np.abs(s1).sum() / np.sqrt(p)          # from n alone, before any readout
    eps = np.where(s1 >= 0, 1, -1).astype(np.int8)
    h = np.zeros(n); h[1:] = eps[idx] * sgn
    V = np.fft.fft(h)
    meas = abs(V[1]) / np.sqrt(p)
    S = np.abs(V)[1:].max() / np.sqrt(p)
    return pred, float(meas), float(S)


def p_floor(p, n):
    e = (n - 1) // 2
    chi = np.zeros(n)
    chi[1:] = [1 if pow(int(x), e, n) == 1 else -1 for x in range(1, n)]
    V = np.abs(np.fft.fft(chi))
    S = V[1:].max() / np.sqrt(p)
    spread = (V[1:].max() - V[1:].min()) / V[1:].max()
    return float(S), float(np.sqrt(n / p)), spread


if __name__ == "__main__":
    rows, _ = load_holdout()
    sel = [rows[0], rows[6], rows[24], rows[60], rows[90]]
    print("=" * 92)
    print("P-CEIL — admissible +-1 target; predicted from n ALONE before any readout")
    print("=" * 92)
    print(f"{'p':>8} {'n':>8} {'predicted':>12} {'measured':>12} {'rel dev':>10} {'S':>9} {'S>2':>5}")
    ok_c = True
    for b, s, p, n, t in sel:
        pred, meas, S = p_ceil(p, n)
        rel = abs(meas - pred) / pred
        ok = rel <= 1e-10 and S > 2
        ok_c &= ok
        print(f"{p:>8} {n:>8} {pred:>12.5f} {meas:>12.5f} {rel:>10.1e} {S:>9.3f} "
              f"{'YES' if S>2 else 'no':>5}")
    print(f"\n  P-CEIL FIRES: {ok_c}")

    print()
    print("=" * 92)
    print("P-FLOOR — h = chi_n (Gauss sum): |V(a)| = sqrt(n) for every a != 0")
    print("=" * 92)
    print(f"{'p':>8} {'n':>8} {'S measured':>12} {'sqrt(n/p)':>12} {'rel dev':>10} {'spread':>10}")
    ok_f = True
    for b, s, p, n, t in sel[:3]:
        S, fl, spread = p_floor(p, n)
        rel = abs(S - fl) / fl
        ok_f &= (rel <= 1e-10 and spread <= 1e-10)
        print(f"{p:>8} {n:>8} {S:>12.6f} {fl:>12.6f} {rel:>10.1e} {spread:>10.1e}")
    print(f"\n  P-FLOOR FIRES: {ok_f}")
    print(f"\n  BOTH MUST-FIRE CONTROLS: {'PASS' if (ok_c and ok_f) else 'FAIL — no verdict'}")
