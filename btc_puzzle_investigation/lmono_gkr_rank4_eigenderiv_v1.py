#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
lmono_gkr_rank4_eigenderiv_v1.py
=================================
L-mono GKR sub-brick 1: the rank-4 eigenvalue bookkeeping FROM the L-polynomial,
done symbolically and then cross-checked DECIDABLY (per
feedback_verify_root_system_against_defining_polynomial: no symbolic root claim
stands until a decidable check agrees).

The symbolic claims under test
------------------------------
L*(a) = T^4 - e1 T^3 + e2 T^2 - e3 T + e4 with the banked coefficient laws
   e1 = -V1,  e2 = e1^2 - eps p  [P32],  e3 = eps p e1,  e4 = p^2,   eps = chi2(-1).
Banked (D2 certificate, exact, 1030 cells): the eigenvalue multiset is
   eps = -1 (p = 3 mod 4):  { a, rho a, -conj(a), -conj(rho a) }   (trace imaginary)
   eps = +1 (p = 1 mod 4):  { a, rho a,  conj(a),  conj(rho a) }   (trace real)
with rho = zeta_3 (or its conjugate), |a| = sqrt(p).

CLAIM 1 (tensor split).  The spectrum is H^1 = W (+) (W (x) psi), psi = order-3
   Kummer char acting as the scalar zeta_3.  The W-plane is the pair {g1} whose
   zeta_3-image {zeta_3 g1} is again a pair of roots (the g = deg gcd(L*(T),
   L*(zeta_3 T)) = 2 law).  Explicitly W = { a, -zeta_3^{-1} conj(a) } (eps=-1)
   or { a, zeta_3^{-1} conj(a) } (eps=+1), i.e. beta = -/+ zeta_3^{-1} conj(a).

CLAIM 2 (tensor-trace identity).  V1 = -(1 + zeta_3) tr(W) = -zeta_6 tr(W),
   because V1 = -(sum of 4 eigenvalues) and tr(W (x) psi) = zeta_3 tr(W).

CLAIM 3 (half-trace reduction).  Writing a = sqrt(p) e^{i phi}, the W eigenvalues
   are sqrt(p) e^{i phi} and sqrt(p) e^{i(pi/3 - phi)}; the det-normalized
   half-trace  cos(theta) = tr(W)/(2 sqrt(det W))  is REAL and equals cos(phi-pi/6),
   and the MEASURED marginal reduces to it exactly:
       eps = -1:  t := Im(V1)/(2 sqrt p) = -cos(theta)
       eps = +1:  t := Re(V1)/(2 sqrt p) = -cos(theta)   (theta = phi + pi/3 here)
   (The overall MINUS is the D2 sign convention V1 = -sum; distributionally
    -cos = cos on the symmetric semicircle, which is why the marginal MC matched
    cos theta.  Last session's t = -sin(theta+pi/3) mishandled only this sign:
    sin(theta+pi/3) = cos(theta-pi/6).)

The script has two independent verification stages.
  STAGE A (abstract, no curve): random phi, both arms -> the multiset ansatz
     reproduces e2,e3,e4 laws AND claims 2,3 hold, for arbitrary a on |a|=sqrt p.
  STAGE B (real curve data): reuse the D2 module's EXACT V1(a) (Z[zeta_n]) at
     several primes/cells/both arms -> claims 1,2,3 hold pointwise on real data.

Float appears only in the degree-4 root readout / angle extraction (as in the D2
certificate); the signal path V1 is exact Z[zeta_n].  Error floor argument: an
exact identity reads at the np.roots conditioning floor (<~1e-9 sqrt p); a false
one is O(1).
"""
import cmath, math, random, sys, os
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import d2_twist_rigidity_certificate_v1 as d2   # curve_points_f, Zz, dft_all, is_prime_int

Z3 = cmath.exp(2j * cmath.pi / 3)          # zeta_3
Z6 = cmath.exp(1j * cmath.pi / 3)          # zeta_6 = 1 + zeta_3


def multiset(alpha, eps):
    """The banked D2 eigenvalue multiset for a given alpha and arm eps=chi2(-1)."""
    rho = Z3
    sgn = -1.0 if eps == -1 else 1.0
    return [alpha, rho * alpha, sgn * alpha.conjugate(), sgn * (rho * alpha).conjugate()]


def elem_sym(roots):
    """e1..e4 (elementary symmetric) of a length-4 root list; L* = T^4 - e1 T^3 + e2 T^2 - e3 T + e4."""
    r = roots
    e1 = sum(r)
    e2 = sum(r[i] * r[j] for i in range(4) for j in range(i + 1, 4))
    e3 = sum(r[i] * r[j] * r[k] for i in range(4) for j in range(i + 1, 4) for k in range(j + 1, 4))
    e4 = r[0] * r[1] * r[2] * r[3]
    return e1, e2, e3, e4


def w_plane(roots, sqp, tol):
    """Identify the W-plane: the two roots r whose zeta_3-multiple is again a root.
    Returns (trW, matched_sources) or (None, ...) if the g=2 structure is absent."""
    src = []
    for i, r in enumerate(roots):
        zr = Z3 * r
        if any(abs(zr - roots[j]) < tol * sqp for j in range(len(roots)) if j != i):
            src.append(r)
    if len(src) != 2:
        return None, src
    return src[0] + src[1], src


def half_trace(trW, detW):
    """det-normalized half-trace cos(theta) = trW / (2 sqrt(detW)), principal sqrt."""
    return trW / (2.0 * cmath.sqrt(detW))


# ----------------------------------------------------------------------------- STAGE A
def stage_a():
    print("=" * 96)
    print(" STAGE A  --  abstract multiset ansatz (no curve): coefficient laws + claims 2,3")
    print("=" * 96)
    rng = random.Random(20260824)
    worst = {"e2": 0.0, "e3": 0.0, "e4": 0.0, "trace_imag_real": 0.0,
             "claim2_V1": 0.0, "claim3_t": 0.0, "halftrace_imag": 0.0}
    N = 40000
    for p in (43, 61, 349, 100003):
        sqp = math.sqrt(p)
        eps = -1 if p % 4 == 3 else 1
        for _ in range(N):
            phi = rng.uniform(0, 2 * math.pi)
            alpha = sqp * cmath.exp(1j * phi)
            roots = multiset(alpha, eps)
            e1, e2, e3, e4 = elem_sym(roots)
            V1 = -e1                                            # law e1 = -V1
            # coefficient laws (these VALIDATE the multiset is L*-consistent)
            worst["e2"] = max(worst["e2"], abs(e2 - (e1 * e1 - eps * p)) / p)
            worst["e3"] = max(worst["e3"], abs(e3 - (eps * p * e1)) / (p * sqp))
            worst["e4"] = max(worst["e4"], abs(e4 - p * p) / (p * p))
            # V1 reality / imaginarity (M4)
            worst["trace_imag_real"] = max(worst["trace_imag_real"],
                                           abs(V1.real if eps == -1 else V1.imag) / sqp)
            # CLAIM 1/2: W-plane and tensor-trace identity V1 = -(1+zeta3) trW
            trW, src = w_plane(roots, sqp, 1e-9)
            assert trW is not None, f"g=2 structure absent (p={p})"
            worst["claim2_V1"] = max(worst["claim2_V1"], abs(V1 - (-(1 + Z3) * trW)) / sqp)
            # CLAIM 3: half-trace reduction
            detW = src[0] * src[1]
            ct = half_trace(trW, detW)
            worst["halftrace_imag"] = max(worst["halftrace_imag"], abs(ct.imag))
            t = (V1.imag if eps == -1 else V1.real) / (2 * sqp)
            worst["claim3_t"] = max(worst["claim3_t"], abs(t - (-ct.real)))
    print(f"   samples: {N} phi x 4 primes x both arms")
    print(f"   e2 law  |e2-(e1^2-eps p)|/p          max {worst['e2']:.2e}")
    print(f"   e3 law  |e3-eps p e1|/(p sqrt p)     max {worst['e3']:.2e}")
    print(f"   e4 law  |e4-p^2|/p^2                 max {worst['e4']:.2e}")
    print(f"   V1 pure imag(eps-1)/real(eps+1)      max {worst['trace_imag_real']:.2e}")
    print(f"   CLAIM 2 V1 = -(1+z3) trW  resid/sqp  max {worst['claim2_V1']:.2e}")
    print(f"   CLAIM 3 half-trace cos(theta) imag=0 max {worst['halftrace_imag']:.2e}")
    print(f"   CLAIM 3 t = -cos(theta)  |resid|     max {worst['claim3_t']:.2e}")
    ok = (worst["e2"] < 1e-10 and worst["e3"] < 1e-10 and worst["e4"] < 1e-10 and
          worst["trace_imag_real"] < 1e-10 and worst["claim2_V1"] < 1e-10 and
          worst["halftrace_imag"] < 1e-10 and worst["claim3_t"] < 1e-10)
    print(f"   STAGE A verdict: {'PASS' if ok else 'FAIL'}")
    return ok


# ----------------------------------------------------------------------------- STAGE B
def stage_b(primes):
    print("=" * 96)
    print(" STAGE B  --  REAL curve data (exact V1(a) via D2 module); claims 1,2,3 pointwise")
    print("=" * 96)
    all_ok = True
    for p in primes:
        n, h = d2.curve_points_f(p)
        assert d2.is_prime_int(n), (p, n)
        ZZ = d2.Zz(n)
        V = d2.dft_all(ZZ, h, n)
        eps = -1 if p % 4 == 3 else 1
        sqp = math.sqrt(p)
        w_g2_fail = 0
        max_claim2 = 0.0
        max_claim3 = 0.0
        max_ht_imag = 0.0
        max_t_vs_ct = 0.0
        cells = 0
        for a in range(1, n):
            e1n = ZZ.embed([-c for c in V[a]])        # e1 = -V1  (V1 exact -> embed for readout)
            V1 = -e1n
            e2n = e1n * e1n - eps * p
            e3n = eps * p * e1n
            roots = list(np.roots([1 + 0j, -e1n, e2n, -e3n, float(p * p)]))
            trW, src = w_plane(roots, sqp, 1e-6)
            if trW is None:
                w_g2_fail += 1
                continue
            cells += 1
            # CLAIM 2: tensor-trace identity (try both zeta3 / zeta3^-1 labelings of the base plane)
            c2a = abs(V1 - (-(1 + Z3) * trW)) / sqp
            # the other labeling: base plane = the zeta3-IMAGE pair, trW' = zeta3 * trW
            c2b = abs(V1 - (-(1 + Z3.conjugate()) * (Z3 * trW))) / sqp
            max_claim2 = max(max_claim2, min(c2a, c2b))
            # CLAIM 3: half-trace
            detW = src[0] * src[1]
            ct = half_trace(trW, detW)
            max_ht_imag = max(max_ht_imag, abs(ct.imag))
            t = (V1.imag if eps == -1 else V1.real) / (2 * sqp)
            max_claim3 = max(max_claim3, abs(t - (-ct.real)))
            max_t_vs_ct = max(max_t_vs_ct, abs(abs(t) - abs(ct.real)))
        arm = "3 mod 4" if eps == -1 else "1 mod 4"
        ok = (w_g2_fail == 0 and max_claim2 < 1e-6 and max_claim3 < 1e-6 and max_ht_imag < 1e-6)
        all_ok = all_ok and ok
        print(f" p={p:>6} n={n:>6} [{arm}]  cells={cells}/{n-1}")
        print(f"     g=2 W-plane found:            fails {w_g2_fail}")
        print(f"     CLAIM 2  V1=-(1+z3)trW /sqp:  max {max_claim2:.2e}")
        print(f"     CLAIM 3  half-trace imag=0:   max {max_ht_imag:.2e}")
        print(f"     CLAIM 3  t = -cos(theta):     max {max_claim3:.2e}  (|t|=|cos| max {max_t_vs_ct:.2e})")
        print(f"     -> {'PASS' if ok else 'FAIL'}")
    return all_ok


if __name__ == "__main__":
    a_ok = stage_a()
    b_ok = stage_b([43, 67, 79, 127, 349, 61])       # both arms; incl. anomalous 61, non-squarefree 67/79
    print("=" * 96)
    print(f" OVERALL: STAGE A {'PASS' if a_ok else 'FAIL'} | STAGE B {'PASS' if b_ok else 'FAIL'}")
    print("=" * 96)
    sys.exit(0 if (a_ok and b_ok) else 1)
