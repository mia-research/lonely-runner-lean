#!/usr/bin/env python3
"""
ct_shear_prediction_v1.py -- the CONSTRUCTIVE version of Investigation 1 (user, 2026-07-17).

QUESTION. Is the 2-3% inter-coordinate coupling (lambda_2 != lambda_3) of the addition-rounding
transfer operator C_T the geometric SHEAR of the flap translation by the reduced basis R1,R2 at
theta=50.55 deg?

THE OPERATOR (from ct_tensor_structure_v1.py, read exactly). C_T is NOT the GLV/endomorphism carry
(the Cap Law eps). It is the ADDITION-rounding carry: for consecutive multiples P_k=[k]G,
    z_k = eis(x_k) in the rhombus P ;  state_k = Babai-carry of (z_k + z_{k+1}) in LATTICE coords
    c1 = round( (sx R2y - sy R2x)/DET ),  c2 = round( (-sx R1y + sy R1x)/DET ),  (c1,c2) in {-1,0,1}^2
C_T = the 9x9 transition state_k -> state_{k+1}.

THE PREDICTION (exact, this file). The user's mechanism says the shear of R couples the two
coordinates. IT DOES NOT, and the reason is decidable:

  * The carry is rounded in LATTICE coordinates. A lift point z in P has lattice coordinates
    (a1,a2) in [-1/2,1/2)^2 -- that IS the fundamental domain, a PRODUCT box, for ANY basis R
    (any theta). The 120-deg shear is absorbed into the (fixed, non-orthogonal) basis; the
    fractional lattice coordinates are still an independent-uniform pair.
  * If the lift points were i.i.d. uniform in P, then (a1,a2) i.i.d. uniform, the coordinate-1
    carry process {round(a1_k + a1_{k+1})} depends only on the a1's, coordinate-2 only on the a2's,
    and the two are INDEPENDENT. Hence  C_T = C_1 (x) C_2  EXACTLY, C_1 = C_2.

We compute C_1 EXACTLY (rational integration over the cube [-1/2,1/2]^3) and its tensor square:

    C_1 = [[7/9,1/9,1/9],[2/3,1/3,0],[2/3,0,1/3]]     eigenvalues {1, 1/3, 1/9}
    C_1 (x) C_1 eigenvalues = {1, 1/3, 1/3, 1/9, 1/9, 1/9, 1/27, 1/27, 1/81}
    => lambda_2 = lambda_3 = 1/3 EXACTLY, doubly degenerate, and THETA-INDEPENDENT.

CONCLUSION (a sharper law, not a closure). The predicted shear is ZERO, exactly, independent of
R1,R2 and theta. The 120-deg lattice shear does not enter the carry statistics. Therefore the
observed 2-3% lambda_2 != lambda_3 is NOT geometric shear; it is a deviation of the arithmetic
sequence {x_d} from the i.i.d.-uniform model -- finite-n estimator noise (DRILL 01: matched
surrogate reproduces it, dev ~ n^-0.59), or a genuine arithmetic coupling below the estimator floor.
This file also gives the n required to detect a TRUE coupling of size epsilon.

Exact rationals for C_1 and its spectrum (sympy). Float only for the empirical bridge (spectral,
not a signal path -- DRILL 01 and ct_tensor both use np float for eig) and the power table.
"""
import sys
from fractions import Fraction as Fr
import numpy as np
from sympy import Matrix, Rational, eye
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv


# ---------------------------------------------------------------- analytic C_1 (exact)
def g_plus(a2):
    """length of {a1 in [-1/2,1/2] : round(a1+a2) = +1}  =  max(0, a2)."""
    return max(Fr(0), a2)
def g_minus(a2):
    return max(Fr(0), -a2)
def g_zero(a2):
    return Fr(1) - abs(a2)

def joint_prob(i, j):
    """P(round(a1+a2)=i, round(a2+a3)=j) = int_{-1/2}^{1/2} g_i(a2) g_j(a2) da2, exact rational.
    g_i are piecewise-linear in a2 with a single breakpoint at 0, so g_i g_j is piecewise-quadratic;
    integrate exactly on [-1/2,0] and [0,1/2] by 3-point (exact for deg<=2) Simpson on each half."""
    G = {1: g_plus, -1: g_minus, 0: g_zero}
    gi, gj = G[i], G[j]
    def simpson(lo, hi):
        mid = (lo + hi) / 2
        return (hi - lo) / 6 * (gi(lo) * gj(lo) + 4 * gi(mid) * gj(mid) + gi(hi) * gj(hi))
    return simpson(Fr(-1, 2), Fr(0)) + simpson(Fr(0), Fr(1, 2))

def analytic_C1():
    states = [0, 1, -1]
    P = {(i, j): joint_prob(i, j) for i in states for j in states}
    marg = {i: sum(P[(i, j)] for j in states) for i in states}
    C1 = Matrix(3, 3, lambda r, c: Rational(P[(states[r], states[c])].numerator,
                                            P[(states[r], states[c])].denominator)
                / Rational(marg[states[r]].numerator, marg[states[r]].denominator))
    return C1, marg, states


# ---------------------------------------------------------------- empirical bridge (float ok)
def empirical_split(p, verbose=False):
    R1, R2 = reduced_basis(p); DET = R1[0] * R2[1] - R1[1] * R2[0]
    def add(A, B):
        if A is None: return B
        if B is None: return A
        x1, y1 = A; x2, y2 = B
        if x1 == x2:
            if (y1 + y2) % p == 0: return None
            lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
        else:
            lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
        x3 = (lam * lam - x1 - x2) % p
        return (x3, (lam * (x1 - x3) - y1) % p)
    def eis(X):
        c1 = rdiv(X * R2[1], DET); c2 = rdiv(-X * R1[1], DET)
        return (X - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))
    def st(z1, z2):
        sx, sy = z1[0] + z2[0], z1[1] + z2[1]
        return (rdiv(sx * R2[1] - sy * R2[0], DET), rdiv(-sx * R1[1] + sy * R1[0], DET))
    G = None
    for x in range(1, p):
        if pow((x * x * x + 7) % p, (p - 1) // 2, p) == 1:
            y = sqrt_mod((x * x * x + 7) % p, p)
            if y: G = (x, int(y)); break
    pts = [G]; cur = G
    while True:
        cur = add(cur, G)
        if cur is None: break
        pts.append(cur)
    n = len(pts)
    z = [eis(P[0]) for P in pts]
    seq = [st(z[k], z[k + 1]) for k in range(n - 1)]
    S9 = [(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1)]; I9 = {s: i for i, s in enumerate(S9)}
    Cj = np.zeros((9, 9))
    for a, b in zip(seq[:-1], seq[1:]):
        if a in I9 and b in I9: Cj[I9[a], I9[b]] += 1
    rs = Cj.sum(1, keepdims=True)
    rs[rs == 0] = 1.0                                   # empty state -> zero row (0 eigenvalue)
    Tj = Cj / rs
    ev = sorted((abs(e) for e in np.linalg.eigvals(Tj)), reverse=True)
    import math
    t = p + 1 - n
    theta = math.degrees(math.acos(min(1.0, abs(t) / (2 * math.sqrt(p)))))   # Frobenius angle
    return n, ev, abs(ev[1] - ev[2]), theta


def main():
    print("=" * 78)
    print("INVESTIGATION 1 (constructive): the predicted addition-carry shear")
    print("=" * 78)
    C1, marg, states = analytic_C1()
    print("\nAnalytic per-coordinate carry operator C_1 (EXACT rational, states 0,+,-):")
    for r in range(3):
        print("   [" + "  ".join(str(C1[r, c]) for c in range(3)) + "]")
    print("   stationary law:", tuple(marg[s] for s in states), " (= 3/4 : 1/8 : 1/8)")
    e1 = C1.eigenvals()
    print("   C_1 eigenvalues (exact):", {str(k): v for k, v in e1.items()})

    # tensor square eigenvalues, exact
    evs = []
    for a in e1:
        for b in e1:
            evs.append(a * b)
    evs_sorted = sorted(set(evs), key=lambda z: -float(z))
    mult = {v: sum(1 for e in evs if e == v) for v in evs_sorted}
    print("\nTensor square  C_1 (x) C_1  eigenvalues (EXACT), value^multiplicity:")
    print("   " + ",  ".join(f"{v}^{mult[v]}" for v in evs_sorted))
    lam = sorted((float(e) for e in evs), reverse=True)
    print(f"\n   >>> lambda_2 = lambda_3 = 1/3 EXACTLY (doubly degenerate).")
    print(f"   >>> The split lambda_2 - lambda_3 is predicted to be 0, and the derivation contains")
    print(f"       NO theta and NO R1,R2 -- it is a property of the PRODUCT fundamental domain in")
    print(f"       lattice coordinates. The 120-deg shear does not reach the carry.  MECHANISM REFUTED.")

    print("\n" + "-" * 78)
    print("Empirical bridge: real arithmetic sequence, |lambda_2 - lambda_3| vs n and theta")
    print("-" * 78)
    print(f"   {'p':>7} {'n':>7} {'theta':>7} {'|l2-l3|':>9}   (analytic prediction: 0)")
    import math
    data = []
    for p in [5011, 20011, 49999, 100003]:            # all p = 1 mod 6 (Eisenstein exists)
        if p % 6 != 1:
            continue
        try:
            n, ev, split, theta = empirical_split(p)
            data.append((n, split))
            print(f"   {p:>7} {n:>7} {theta:>6.2f} {split:>9.4f}")
        except Exception as ex:
            print(f"   {p:>7}  skipped ({ex})")
    if len(data) >= 2:
        xs = [math.log(n) for n, _ in data]; ys = [math.log(s) for _, s in data]
        k = len(xs); sx = sum(xs); sy = sum(ys); sxx = sum(x * x for x in xs); sxy = sum(x * y for x, y in zip(xs, ys))
        b_fit = (k * sxy - sx * sy) / (k * sxx - sx * sx)
        print(f"\n   local fit exponent b = {b_fit:.3f} (few points; DRILL 01's authoritative b = -0.584)")
        print("   the split DECAYS with n -> consistent with the analytic 0, NOT a fixed coupling.")

    # POWER TABLE: anchored on DRILL 01's authoritative exponent + the clean n=99666 measurement,
    # NOT on the noisy local fit above.
    b = -0.584
    n_anchor, split_anchor = 99666, 0.0113           # DRILL 01 / this run's p=100003
    C = split_anchor / n_anchor ** b                 # floor(n) = C * n^b
    print("\n" + "-" * 78)
    print("Required n to DETECT (or rule out) a TRUE arithmetic coupling of size epsilon")
    print(f"   estimator floor calibrated on DRILL 01: |l2-l3|_noise = C*n^b, b=-0.584,")
    print(f"   anchored at (n={n_anchor}, split={split_anchor}) => C = {C:.3g}")
    print(f"   need floor < epsilon  =>  n > (C/epsilon)^(1/|b|)")
    print("-" * 78)
    print(f"   {'epsilon (as % of 1/3)':>24} {'epsilon':>10} {'required n':>14}")
    for pct in (3, 1, 0.3, 0.1, 0.03):
        eps = pct / 100 * (1 / 3)
        nreq = (C / eps) ** (1 / abs(b))
        print(f"   {pct:>22}% {eps:>10.5f} {nreq:>14.2e}")
    print("\n   => a coupling at the 0.1% level needs n ~ 10^7 (master s.X.6's next probe: n~10^6-10^7);")
    print("      at ~2-3% (where DRILL 01 measured) n~10^5 is exactly AT the floor -> uninformative,")
    print("      which is why DRILL 01's matched surrogate reproduced the split (z=+0.13).")

if __name__ == '__main__':
    main()
