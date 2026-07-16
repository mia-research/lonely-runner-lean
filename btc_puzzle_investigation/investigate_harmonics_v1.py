#!/usr/bin/env python3
"""
investigate_harmonics_v1.py -- threads #1 & #2 (positive hunt): characterize what d-structure the
transfer-operator eigenvectors encode.  EXTEND, do not bound.

#1 lambda_3 eigenvector is 60->85% mu_3-covariant (v25): a GLV harmonic residue.  What is it?
   - phi_k(P_d) = v_k[cell(x_d)]; DFT phi_k^(a) = correlation with the scalar character e_n(a d).
   - mu_3-covariance phi(beta x)=zeta phi(x) + GLV (beta x_d = x_{lambda d}) => phi^(a) organized on
     lambda-ORBITS of frequencies {a, lambda a, lambda^2 a}.  Where does |phi^| concentrate?  Low
     freq (smooth) or specific arithmetic freq?  Can we IDENTIFY phi explicitly (sextant/angle harmonic)?
#2 joint x-cell x y-cell lambda_2 (z=6.4, v25): does the slow joint mode ACCESS the odd (y) half that
   x-alone cannot?  odd-fraction, mu_3-content, top frequencies.

Float carve-out: spectral display, no key in path.
"""
import numpy as np, math, cmath
from fractions import Fraction as Fr
from sympy import isprime
import conservation_spectrum_v2 as C
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import reduced_basis
from hybrid_char_sum_v1 import curve_points_order
Z = cmath.exp(2j*math.pi/3)


def prime(lo, hi):
    return next(q for q in range(lo, hi) if isprime(q) and q % 3 == 1 and isprime(curve_points_order(q)))

def glv(xs, p, n):
    for l in [l for l in range(2, n) if pow(l, 3, n) == 1]:
        b = None; ok = True
        for d in range(1, 25):
            if xs[d] is None or xs[(l*d) % n] is None or xs[d] == 0:
                continue
            bb = xs[(l*d) % n]*pow(xs[d], p-2, p) % p
            if b is None: b = bb
            elif bb != b: ok = False; break
        if ok and b not in (None, 1):
            return l, b
    return None, None

def concentration(mag):
    m = np.abs(mag)**2; s = m.sum()
    if s == 0: return 0.0, []
    pr = (s*s)/np.sum(m**2)          # participation ratio (low = concentrated)
    top = list(np.argsort(-m)[:6])
    return float(pr), top

def dft_of_mode(v, cellfn, xs, p, n, K):
    phi = np.array([0j]+[v[cellfn(xs[d], K)] if xs[d] is not None else 0 for d in range(1, n)], dtype=complex)
    ph = np.fft.fft(phi)/n           # phi^(a) for all a  (correlation with e_n(a d))
    ph[0] = 0
    return phi, ph


def main():
    print("="*82)
    print("HARMONIC INVESTIGATION -- threads #1 (lambda3 mu3-harmonic) & #2 (joint z=6.4 shadow)")
    print("="*82)
    for lo, hi in [(400, 700), (1000, 1400), (2000, 2400)]:
        p = prime(lo, hi); n = curve_points_order(p); G = C.curve_gen(p)
        xs, ys = C.orbit(G, p, n); lam, beta = glv(xs, p, n); cell = C.cell_fn(p); K = 4
        print("\n p=%d n=%d  GLV lambda=%s beta=%s" % (p, n, lam, beta))

        # x-cell transfer eigenvectors
        lab = [cell(xs[d], K) if xs[d] is not None else 0 for d in range(1, n)]
        M = C.transfer_matrix(lab, K*K); ev, evec = C.spectrum(M)
        for idx, tag in [(1, "lam2"), (2, "lam3")]:
            v = evec[:, idx]
            phi, ph = dft_of_mode(v, cell, xs, p, n, K)
            pr, top = concentration(ph)
            # lambda-orbit structure: is |phi^(a)| = |phi^(lambda a)|?
            a = np.arange(n); mag = np.abs(ph)
            orb = float(np.corrcoef(mag, mag[(lam*a) % n])[0, 1]) if lam else float("nan")
            # is it concentrated at LOW freq? mass in |a|<n/10 (a or n-a small)
            lowmask = (a < n//10) | (a > n - n//10)
            lowfrac = float(np.sum(mag[lowmask]**2)/np.sum(mag**2))
            print("   %s |lam|=%.3f  PR/n=%.3f (low=concentrated)  lam-orbit corr(|phi^|)=%.2f  low-freq mass=%.2f  top-a=%s"
                  % (tag, abs(ev[idx]), pr/n, orb, lowfrac, top[:5]))

        # try to IDENTIFY lambda3: correlate with explicit mu3 candidate = e^{2pi i * (x-cell mu3-phase)}
        # candidate: the GLV orbit index / a smooth angular harmonic of the lift
        v3 = evec[:, 2]
        # build candidate psi(x) = value that is mu3-covariant by construction: use beta-orbit position
        # (rank of x within {x,beta x,beta^2 x}) -> a discrete mu3 phase
        def orbit_phase(x):
            o = [x, beta*x % p, beta*beta*x % p]
            return o.index(min(o))          # 0/1/2, NOT beta-equivariant but a mu3-orbit label
        psi = np.array([0j]+[cmath.exp(2j*math.pi*orbit_phase(xs[d])/3) if xs[d] is not None else 0 for d in range(1, n)], dtype=complex)
        phi3 = np.array([0j]+[v3[cell(xs[d], K)] if xs[d] is not None else 0 for d in range(1, n)], dtype=complex)
        ide = abs(np.vdot(psi[1:], phi3[1:]))/(np.linalg.norm(psi[1:])*np.linalg.norm(phi3[1:])+1e-12)
        print("   lam3 vs mu3-orbit-phase observable: |overlap|=%.3f" % ide)

        # #2 joint x-cell x y-cell lambda_2: does it access the ODD half?
        Kj = 4
        jlab = [((cell(xs[d], Kj) if xs[d] is not None else 0)*Kj + (min(Kj-1, ys[d]*Kj//p) if ys[d] is not None else 0)) for d in range(1, n)]
        Mj = C.transfer_matrix(jlab, Kj*Kj*Kj); evj, evecj = C.spectrum(Mj)
        vj = evecj[:, 1]
        phij = np.array([0j]+[vj[((cell(xs[d], Kj) if xs[d] is not None else 0)*Kj + (min(Kj-1, ys[d]*Kj//p) if ys[d] is not None else 0))] if xs[d] is not None else 0 for d in range(1, n)], dtype=complex)
        d = np.arange(n)
        Fe = 0.5*(phij + phij[(n-d) % n]); Fo = 0.5*(phij - phij[(n-d) % n])
        oddfrac = float(np.sum(np.abs(Fo[1:])**2)/(np.sum(np.abs(phij[1:])**2)+1e-12))
        print("   [#2] joint x-cell*y-cell lam2=%.3f  ODD-in-d fraction of its eigenvector = %.3f  %s"
              % (abs(evj[1]), oddfrac, "(accesses the odd/shadow half)" if oddfrac > 0.2 else "(x-visible/even)"))
    print("\n[done]")


if __name__ == '__main__':
    main()
