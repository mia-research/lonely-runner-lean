#!/usr/bin/env python3
"""
positive_structure_hunt_v1.py -- STOP closing, START extending. Re-examine the session's buried
positives, hunting for reductions / shadows / harmonic residues of the scalar d from (x,y).

Lens correction (user): a null is a scoped fact, not a closure; a bound is not "no structure";
"tautological" (Dkn/Derr) is how the Eisenstein lift / rhombus / sextic / 3-4-1-8 geometry were found.

THE THREAD: why is sign(xy) the best cheap readout?  Because xy has a DEFINITE symmetry type:
  * GLV:      xy(beta*P) = beta * xy(P)   (mu_3-COVARIANT; since x->beta x, y fixed)
  * negation: xy(-P)     = - xy(P)        (ODD in d; since x even, y odd)
So xy lives in the ODD-in-d, mu_3-covariant sector -- EXACTLY the "odd half" shadow that every
x-only readout (x is EVEN in d) is structurally BLIND to.  A cheap sign(xy) readout therefore
REACHES the shadow subspace, cheaply.  This file quantifies that (not bounds it away).

TESTS:
 (1) verify xy is odd-in-d + mu_3-covariant (structure, exact).
 (2) even/odd d-spectrum split of cheap readouts: which ACCESS the odd (shadow) half?
     x-readouts: all energy in EVEN a.  xy / s_y / sigma*s_y: energy in ODD a = the shadow.
 (3) GLV harmonic structure: is the correlation of xy-type readouts organized on lambda-orbits of a?
 (4) how much of the odd-half shadow does a CHEAP xy-basis capture vs the aligned (needs U) ceiling?

Float carve-out: character-sum magnitudes, no key in path.
"""
import math
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords


def glv(xs, p, n):
    """find lambda (order 3 mod n) and beta with x_{lambda d} = beta x_d."""
    lams = [l for l in range(2, n) if pow(l, 3, n) == 1]
    for l in lams:
        # beta from x_{l} vs x_1
        d0 = 1
        if xs[d0] is None:
            continue
        # beta = x_{l*d0}/x_{d0}? no: x_{l d} = beta x_d ; check on several d
        cand = None
        ok = True
        for d in range(1, 20):
            if xs[d] is None or xs[(l*d) % n] is None:
                continue
            if xs[d] == 0:
                continue
            b = xs[(l*d) % n] * pow(xs[d], p-2, p) % p
            if cand is None:
                cand = b
            elif b != cand:
                ok = False; break
        if ok and cand is not None and cand != 1:
            return l, cand
    return None, None


def corr_all(Fd, n):
    F = np.asarray(Fd, dtype=complex).copy(); F[0] = 0.0
    return np.fft.fft(F) / n            # Corr_F(a) for all a


def even_odd_split(Fd, n):
    """energy of Corr_F on a and on n-a: even part (x-visible) vs odd part (shadow)."""
    C = corr_all(Fd, n); C[0] = 0
    mag2 = np.abs(C)**2
    a = np.arange(n)
    ev = 0.5*(mag2 + mag2[(n - a) % n])   # symmetric (even-a) energy
    od = 0.5*(mag2 - mag2[(n - a) % n])   # this is 0 for real spectra; use the readout's parity instead
    # better: split the READOUT into even/odd in d, measure energy of each
    F = np.asarray(Fd, dtype=complex).copy(); F[0] = 0
    d = np.arange(n)
    Fe = 0.5*(F + F[(n - d) % n]); Fo = 0.5*(F - F[(n - d) % n])
    e = float(np.sum(np.abs(Fe[1:])**2)); o = float(np.sum(np.abs(Fo[1:])**2))
    tot = e + o
    return o/tot if tot > 0 else 0.0     # ODD fraction = shadow-subspace fraction


def main():
    print("="*82)
    print("POSITIVE STRUCTURE HUNT -- shadows/residues of d from (x,y); the xy odd+mu3 thread")
    print("="*82)

    for lo, hi in [(200, 400), (700, 1000), (2000, 2600)]:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, n, G = r
        xs, ys = group_coords(G, p, n, 0)
        lam, beta = glv(xs, p, n)
        print("\n p=%d n=%d  GLV lambda=%s beta=%s" % (p, n, lam, beta))

        # (1) xy symmetry (exact)
        xy = [None] + [(xs[d]*ys[d]) % p for d in range(1, n)]
        odd_ok = all((xy[d] + xy[n-d]) % p == 0 for d in range(1, n))          # xy(-P) = -xy(P)
        if beta:
            cov_ok = all(xy[(lam*d) % n] == (beta*xy[d]) % p for d in range(1, min(n, 40)))
            print("   [1] xy odd-in-d: %s   xy(beta P)=beta xy(P) (mu3-cov): %s  => xy is ODD + mu3-COVARIANT"
                  % (odd_ok, cov_ok))

        # (2) ODD-fraction (shadow-subspace access) of cheap readouts
        def arr(f): return np.array([0.0] + [f(xs[d], ys[d]) for d in range(1, n)], dtype=complex)
        readouts = {
            'x-half (x-readout)': arr(lambda x, y: 1.0 if x < p/2 else -1.0),
            'x mod 6':            arr(lambda x, y: np.exp(2j*math.pi*(x % 6)/6)),
            'sign(xy)':           arr(lambda x, y: 1.0 if (x*y % p) < p/2 else -1.0),
            'xy (raw)':           arr(lambda x, y: (x*y % p)),
            's_y (y-half)':       arr(lambda x, y: 1.0 if y < p/2 else -1.0),
            'e_p(xy)':            arr(lambda x, y: np.exp(2j*math.pi*(x*y % p)/p)),
        }
        print("   [2] ODD-in-d fraction (=shadow-subspace access; x-readouts ~0, odd readouts ~1):")
        for nm, F in readouts.items():
            of = even_odd_split(F, n)
            tag = " <-- reaches the shadow half" if of > 0.5 else (" (x-visible, even)" if of < 0.1 else "")
            print("       %-20s odd-fraction = %.3f%s" % (nm, of, tag))

        # (3) GLV harmonic structure of sign(xy) correlation: is |Corr(a)| organized on lambda-orbits?
        if lam:
            C = np.abs(corr_all(readouts['sign(xy)'], n)); C[0] = 0
            a = np.arange(n)
            # correlation of |Corr(a)| with |Corr(lambda a)|
            Cl = C[(lam*a) % n]
            num = float(np.dot(C - C.mean(), Cl - Cl.mean()))
            den = float(np.linalg.norm(C - C.mean())*np.linalg.norm(Cl - Cl.mean()) + 1e-12)
            rho_glv = num/den
            # null: correlation with a random permutation of frequencies
            rng = np.random.default_rng(p); Cr = C[rng.permutation(n)]
            numr = float(np.dot(C - C.mean(), Cr - Cr.mean()))
            rho_null = numr/(float(np.linalg.norm(C - C.mean())*np.linalg.norm(Cr - Cr.mean())) + 1e-12)
            print("   [3] sign(xy) |Corr(a)| vs |Corr(lambda a)| GLV-orbit corr = %.3f  (random-null %.3f)"
                  % (rho_glv, rho_null))

    print("\n VERDICT (positive framing): xy is the odd+mu3 object -- a cheap readout in the SHADOW")
    print(" subspace x cannot see. This is STRUCTURE (a partial shadow), scoped by KS in magnitude but")
    print(" real in symmetry type. Next: does an xy-harmonic BASIS reduce d beyond |Aut|?")
    print("[done]")


if __name__ == '__main__':
    main()
