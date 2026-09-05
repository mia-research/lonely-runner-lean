#!/usr/bin/env python3
"""Part B (pre-registered): is `eps` an ARITHMETIC object -- does the flap label
carry a multiplicative character / residue-symbol of x?

Implements the experiment-designer pre-registration spec verbatim:
  STATISTIC     : Pearson chi^2 (obs as exact Fraction; null via matched permutation)
  FEATURES      : chi2, chi3, chi6, size6(=6*(x^2 mod p)//p)   [chi3/chi6 = construction-
                  entangled with eps's order-3 machinery -> a hit is an IDENTITY to prove,
                  not leakage; chi2 & size6 carry the thesis]
  TABLES        : pooled 3xk ; T_core (eps=0 vs flap) x k ; T_flapsign (eps=1 vs 2) x k
  NEG CONTROL   : fixed-margin permutation null; verdict = integer exceedance count
  POS CONTROLS  : norm-band nb (MUST fire), sextant, GLM threshold indicator
  PLANTED       : power calibration -- plant a known eps-dependence at fraction f
  SCOPE         : exhaustive x in [1,p); p1=100003 in-sample, p2=100057 out-of-sample
Verdict is decided OUT-OF-SAMPLE per the spec's falsification table.

No-float rule: chi^2 is a MONOTONE STATISTIC ranked against a matched permutation
null (the one float use the folder rule explicitly permits); the verdict is an
integer exceedance count, never a float threshold on the data. obs chi^2 also
reported as an exact Fraction.
"""
import sys, time
from fractions import Fraction
import numpy as np
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import enorm
from glv_fundamental_domain_law_v1 import cube_roots, sextant

RNG = np.random.default_rng(20260718)


def chi2_float(table):
    """Pearson chi^2 as float (fast; used only for permutation ranking)."""
    t = table.astype(np.float64)
    n = t.sum()
    R = t.sum(1, keepdims=True); C = t.sum(0, keepdims=True)
    E = R @ C / n
    m = E > 0
    return float(((t[m] - E[m])**2 / E[m]).sum())


def chi2_exact(table):
    """Pearson chi^2 as an exact Fraction: n*(sum N_ij^2/(R_i C_j)) - n."""
    t = table
    n = int(t.sum())
    R = t.sum(1); C = t.sum(0)
    s = Fraction(0)
    rows, cols = t.shape
    for i in range(rows):
        if R[i] == 0: continue
        for j in range(cols):
            if C[j] == 0 or t[i, j] == 0: continue
            s += Fraction(int(t[i, j])**2, int(R[i]) * int(C[j]))
    return n * s - n


def cramers_v(chi2, n, rows, cols):
    q = min(rows, cols)
    return (chi2 / (n * (q - 1)))**0.5 if q > 1 and n else 0.0


def mi_nats(table):
    t = table.astype(np.float64); n = t.sum()
    R = t.sum(1, keepdims=True); C = t.sum(0, keepdims=True)
    P = t / n; PR = R / n; PC = C / n
    m = P > 0
    return float((P[m] * np.log(P[m] / (PR @ (PC) )[m])).sum())


def build_table(rows_lab, cols_lab, nrows, ncols):
    idx = rows_lab.astype(np.int64) * ncols + cols_lab.astype(np.int64)
    return np.bincount(idx, minlength=nrows * ncols).reshape(nrows, ncols)


def perm_test(rows_lab, cols_lab, nrows, ncols, B):
    """obs chi^2 + integer exceedance count under fixed-margin permutation null."""
    obs_tab = build_table(rows_lab, cols_lab, nrows, ncols)
    obs = chi2_float(obs_tab)
    col = cols_lab.copy()
    exc = 0
    for _ in range(B):
        RNG.shuffle(col)
        if chi2_float(build_table(rows_lab, col, nrows, ncols)) >= obs:
            exc += 1
    return obs, exc, obs_tab


def compute_features(p):
    eis, eps = build(p)
    b1, b2 = cube_roots(p)
    e6 = (p - 1) // 6
    # map the 6 distinct 6th-roots-of-unity to 0..5
    root = pow(_prim_root(p), e6, p)
    six = {}
    r = 1
    for j in range(6):
        six[r] = j; r = (r * root) % p
    xs = np.arange(1, p, dtype=np.int64)
    eps_v = np.empty(p - 1, np.int8)
    chi2 = np.empty(p - 1, np.int8)
    chi3 = np.empty(p - 1, np.int8)
    chi6 = np.empty(p - 1, np.int8)
    size6 = np.empty(p - 1, np.int8)
    nb = np.empty(p - 1, np.int16)
    sext = np.empty(p - 1, np.int8)
    thr = np.empty(p - 1, np.int8)
    e2 = (p - 1) // 2; e3 = (p - 1) // 3
    for i, x in enumerate(range(1, p)):
        z = eis(x); N = enorm(z)
        eps_v[i] = eps(x)
        chi2[i] = 0 if pow(x, e2, p) == 1 else 1
        t3 = pow(x, e3, p); chi3[i] = 0 if t3 == 1 else (1 if t3 == b1 else 2)
        chi6[i] = six[pow(x, e6, p)]
        size6[i] = (6 * ((x * x) % p)) // p
        nb[i] = (16 * N) // p
        sext[i] = sextant(z[0], z[1])
        thr[i] = 1 if 16 * N < 3 * p else 0
    return dict(eps=eps_v, chi2=chi2, chi3=chi3, chi6=chi6, size6=size6,
                nb=nb, sext=sext, thr=thr)


def _prim_root(p):
    from sympy.ntheory.residue_ntheory import primitive_root
    return primitive_root(p)


def n_labels(a):
    return int(a.max()) + 1


def run_prime(p, B_char=20000, B_pos=2000, label=""):
    print("=" * 78)
    print(f"PRIME p={p}  ({label})   exhaustive x in [1,p),  n={p-1}")
    t0 = time.time()
    F = compute_features(p)
    eps = F['eps']
    flap_mask = eps != 0
    results = {}

    def one(name, feat, B):
        k = n_labels(feat)
        # pooled 3xk
        obs, exc, tab = perm_test(eps, feat, 3, k, B)
        V = cramers_v(obs, p - 1, 3, k); MI = mi_nats(tab)
        # T_core: [eps==0] vs [eps!=0]
        core_lab = (eps != 0).astype(np.int64)
        obs_c, exc_c, _ = perm_test(core_lab, feat, 2, k, B)
        # T_flapsign: eps==1 vs eps==2 on flap points
        if flap_mask.sum() > 0 and n_labels(eps[flap_mask]) > 1:
            fl = (eps[flap_mask] == 2).astype(np.int64)
            fc = feat[flap_mask]
            kk = n_labels(fc)
            obs_f, exc_f, _ = perm_test(fl, fc, 2, kk, B)
        else:
            obs_f, exc_f = float('nan'), -1
        results[name] = (obs, exc, V, MI, obs_c, exc_c, obs_f, exc_f, B)
        print(f"  {name:7s} k={k:<2d} | pooled chi2={obs:12.2f} exc={exc}/{B} V={V:.4f} MI={MI:.2e}"
              f" | T_core exc={exc_c}/{B} | T_flapsign exc={exc_f}/{B}")

    print("-- NEGATIVE/character features (chi2 & size6 = load-bearing; chi3/chi6 = entangled) --")
    for nm in ['chi2', 'size6', 'chi3', 'chi6']:
        one(nm, F[nm], B_char)
    print("-- POSITIVE controls (norm band MUST fire; else apparatus dead) --")
    for nm in ['nb', 'sext', 'thr']:
        one(nm, F[nm], B_pos)
    print(f"  [elapsed {time.time()-t0:.1f}s]")
    return results, F


def planted_power(F, p, fracs=(0.05, 0.02, 0.01, 0.005), B=20000):
    """Power calibration: plant a deterministic eps-dependence in a fake character on
    fraction f of x, independent matched-marginal elsewhere; confirm the test fires."""
    print("-- PLANTED power calibration (chi2-shaped fake character vs eps) --")
    eps = F['eps']; n = p - 1
    base = F['chi2'].copy()  # marginal template (k=2)
    for f in fracs:
        plant = base.copy()
        m = RNG.random(n) < f
        # on planted rows, make the fake char a deterministic function of eps (eps==0 -> 0 else 1)
        plant[m] = (eps[m] != 0).astype(np.int8)
        # elsewhere: independent draw with same 2-symbol marginal
        rest = ~m
        plant[rest] = RNG.integers(0, 2, size=rest.sum()).astype(np.int8)
        obs, exc, tab = perm_test(eps, plant, 3, 2, B)
        V = cramers_v(obs, n, 3, 2)
        fires = "FIRES" if exc == 0 else "no"
        print(f"   f={f:<6} planted: chi2={obs:10.2f} exc={exc}/{B} V={V:.4f}  -> {fires}")


if __name__ == "__main__":
    r1, F1 = run_prime(100003, label="in-sample")
    planted_power(F1, 100003)
    r2, F2 = run_prime(100057, label="OUT-OF-SAMPLE confirm")
    print("=" * 78)
    print("VERDICT is decided by cross-referencing p1 & p2 against the pre-reg falsification table.")
