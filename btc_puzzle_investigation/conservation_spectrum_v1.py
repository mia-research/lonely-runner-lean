#!/usr/bin/env python3
"""
conservation_spectrum_v1.py — approximate conservation laws / metastable soft modes.

Thermodynamic lens: security = a critical, quantum-chaotic (Porter-Thomas) system. Magnitude
structure is closed (no scar). The remaining place a leak can live = the PHASES, specifically
a near-conserved quantity beyond mu_6 = a soft mode whose phase-coherence outlives thermal.

Object: the coarse-grained TRANSFER (Koopman) operator of a computable label under the walk
step P -> P+G (i.e. d -> d+1).  For label l(d) in a finite alphabet,
    M[i,j] = #{d : l(d)=i, l(d+1)=j} / #{d : l(d)=i}   (row-stochastic).
Spectrum:  lambda=1 = Perron (the trivial constant conservation).  |lambda| ON the unit
circle = an EXACT conservation law (a character/symmetry).  |lambda| NEAR 1 but < 1 = an
APPROXIMATE conservation law = a metastable mode = slow phase-coherence = a soft spot.
Fully-mixing (thermal) => all non-Perron |lambda| at the noise floor (-> 0 as n grows).

Test: real orbit vs THERMAL NULL (shuffle the d-order: destroys all temporal/conservation
structure, keeps the label marginal) vs random-d-generator control. Does the real |lambda_2|
sit ABOVE the shuffle floor, and does it PERSIST (conserved) or DECAY with n (thermal)?
mu_6-covariant labels will show the KNOWN mu_6 modes; a mu_6-INVARIANT label isolates
'beyond mu_6'.  Labels are exact integers; eigenvalues are spectral display (no key in path).
"""
import numpy as np, math
from fractions import Fraction as Fr
from sympy import isprime
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import reduced_basis
from hybrid_char_sum_v1 import find_point, padd, curve_points_order, legendre, tonelli


def curve_gen(p):
    for x0 in range(1, p):
        r = (x0**3 + 7) % p
        if legendre(r, p) == 1:
            return (x0, tonelli(r, p))


def orbit(G, p, n):
    xs = [None]*n; ys = [None]*n; a = None
    for d in range(1, n):
        a = padd(a, G, p); xs[d], ys[d] = a
    return xs, ys


def transfer_spectrum(labels, nstates):
    """row-stochastic transfer matrix of the sequence labels[d]->labels[d+1], its eigenvalues."""
    L = np.zeros((nstates, nstates))
    seq = labels
    for d in range(len(seq)-1):
        L[seq[d], seq[d+1]] += 1
    rs = L.sum(1, keepdims=True); rs[rs == 0] = 1
    M = L / rs
    ev = np.linalg.eigvals(M)
    ev = ev[np.argsort(-np.abs(ev))]
    return ev


def main():
    print("CONSERVATION SPECTRUM: transfer operator of a coarse label under P->P+G.")
    print("|lambda_2| near 1 & PERSISTENT = approx conservation law (soft mode). Thermal => ->0.\n")
    for lo, hi in [(400, 700), (1000, 1400), (2500, 3000)]:
        p = next(q for q in range(lo, hi) if isprime(q) and q % 3 == 1 and isprime(curve_points_order(q)))
        n = curve_points_order(p); G = curve_gen(p)
        xs, ys = orbit(G, p, n)
        eis, eps = build(p)
        R1, R2 = reduced_basis(p); R1 = tuple(R1); R2 = tuple(R2); DET = R1[0]*R2[1]-R1[1]*R2[0]
        def cell(x, k):
            u = Fr(eis(x)[0]*R2[1]-eis(x)[1]*R2[0], DET); v = Fr(eis(x)[1]*R1[0]-eis(x)[0]*R1[1], DET)
            iu = min(k-1, int((u + Fr(1, 2)) * k)); iv = min(k-1, int((v + Fr(1, 2)) * k))
            return iu * k + iv
        # labels (all functions of the POINT, computable):
        K = 4
        lab_cell = [cell(xs[d], K) if xs[d] is not None else 0 for d in range(n)]       # K*K lift cell (mu6-covariant)
        # norm-band (mu6-INVARIANT: isolates 'beyond mu6')
        def nb(x):
            u = Fr(eis(x)[0]*R2[1]-eis(x)[1]*R2[0], DET); v = Fr(eis(x)[1]*R1[0]-eis(x)[0]*R1[1], DET)
            return min(5, int((u*u-u*v+v*v) * 6 / Fr(1)))  # crude norm band
        lab_norm = [nb(xs[d]) % 6 if xs[d] is not None else 0 for d in range(n)]
        rng = np.random.default_rng(p)
        for name, lab, ns in [("K4 lift-cell (mu6-cov)", lab_cell, K*K),
                              ("norm-band (mu6-INV)", lab_norm, 6)]:
            lab = np.array(lab[1:])                       # drop identity
            ev = transfer_spectrum(lab, ns)
            l2 = abs(ev[1]) if len(ev) > 1 else 0
            # thermal null: shuffle temporal order
            sh = lab.copy(); rng.shuffle(sh)
            evs = transfer_spectrum(sh, ns)
            l2s = abs(evs[1]) if len(evs) > 1 else 0
            top = ", ".join(f"{abs(z):.3f}" for z in ev[1:5])
            print(f"  p={p:>4} [{name:22}]: |lam2..5|=({top})  shuffle|lam2|={l2s:.3f}  "
                  f"real/shuf={l2/max(l2s,1e-9):.2f}")
        print()
    print("READ: real |lam2| ~ shuffle floor, and DECAYING across p => thermal, NO soft mode")
    print("      beyond mu_6.  real |lam2| >> shuffle AND flat/growing across p => a metastable")
    print("      near-conservation law = the phase-coherent soft spot the lens predicts as the")
    print("      only remaining place a computable leak can live.")


if __name__ == "__main__":
    main()
