#!/usr/bin/env python3
"""
conservation_spectrum_v2.py -- Item #3: the two OWED refinements from v18's self-audit
("SCOPE (do not re-dismiss)"):

 (a) The x-cell transfer |lambda_2| ~ 1.8x floor was ATTRIBUTED to mu_6 WITHOUT checking the
     EIGENVECTOR (the prior attempt mis-labeled by scalar-d -> artifact). Here we check the
     eigenvector's mu_3 identity DIRECTLY on x-values (mu_6 acts on x-coords only as mu_3 = <beta>;
     [-1] fixes x). Pull lambda_2's eigenvector v2 back to phi(x)=v2[cell(x)] and compute
        A = sum_x phi(beta x) conj(phi(x)) / sum_x |phi(x)|^2.
     |A| ~ 1 with arg(A) ~ +-120deg  <=>  v2 is a NONTRIVIAL-mu_3 covariant charge (attribution
     CONFIRMED). arg(A) ~ 0 => mu_3-TRIVIAL (the 1.8x is a generic lift-geometry correlation,
     mis-attributed). This sidesteps the axis-aligned-grid rotation that caused the artifact.

 (b) The joint soft-mode test used y-PARITY only. Here we test GENERAL y-readouts (y-cell, y mod m,
     y-half, joint x-cell x y-cell) for a metastable soft mode: transfer |lambda_2| real vs thermal
     shuffle, scaling across p. Thermal (real/shuffle -> 1, decaying) => no soft mode beyond mu_6.

FLOAT CARVE-OUT: labels are exact integers; eigenvalues/vectors are spectral display, no key in
path (same carve-out as glv_closure_verification / conservation_spectrum_v1).
"""
import numpy as np, math
from fractions import Fraction as Fr
from sympy import isprime
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import reduced_basis
from hybrid_char_sum_v1 import padd, curve_points_order, legendre, tonelli


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

def beta_of(p):
    e = (p-1)//3; g = 2
    while pow(g, e, p) == 1:
        g += 1
    return pow(g, e, p)

def transfer_matrix(labels, nstates):
    L = np.zeros((nstates, nstates))
    for d in range(len(labels)-1):
        L[labels[d], labels[d+1]] += 1
    rs = L.sum(1, keepdims=True); rs[rs == 0] = 1
    return L / rs

def spectrum(M):
    ev, evec = np.linalg.eig(M)
    order = np.argsort(-np.abs(ev))
    return ev[order], evec[:, order]


def cell_fn(p):
    eis, eps = build(p)
    R1, R2 = reduced_basis(p); R1 = tuple(R1); R2 = tuple(R2)
    DET = R1[0]*R2[1]-R1[1]*R2[0]
    def coeffs(x):
        z = eis(x)
        u = Fr(z[0]*R2[1]-z[1]*R2[0], DET); v = Fr(z[1]*R1[0]-z[0]*R1[1], DET)
        return u, v
    def cell(x, k):
        u, v = coeffs(x)
        iu = min(k-1, int((u + Fr(1, 2)) * k)); iv = min(k-1, int((v + Fr(1, 2)) * k))
        return iu*k + iv
    return cell


def test_a_eigenvector_mu3(p, K=4):
    n = curve_points_order(p); G = curve_gen(p); xs, ys = orbit(G, p, n)
    beta = beta_of(p); cell = cell_fn(p)
    lab = [cell(xs[d], K) if xs[d] is not None else 0 for d in range(1, n)]
    M = transfer_matrix(lab, K*K)
    ev, evec = spectrum(M)
    out = {}
    for idx, tag in [(0, 'Perron l1(calib)'), (1, 'l2'), (2, 'l3')]:
        v = evec[:, idx]
        # pull back to phi(x) = v[cell(x)] over all x-coords on the curve
        A_num = 0j; norm = 0.0
        for x in range(p):
            if legendre((x**3+7) % p, p) < 0:
                continue
            phix = v[cell(x, K)]
            phibx = v[cell((beta*x) % p, K)]
            A_num += phibx * np.conj(phix); norm += abs(phix)**2
        A = A_num / norm if norm > 0 else 0j
        out[tag] = (abs(ev[idx]), abs(A), math.degrees(np.angle(A)))
    return out

def test_b_general_y(p_list, K=4):
    rows = []
    for p in p_list:
        n = curve_points_order(p); G = curve_gen(p); xs, ys = orbit(G, p, n)
        cell = cell_fn(p)
        rng = np.random.default_rng(p)
        def score(lab, ns):
            lab = np.array(lab[1:])
            M = transfer_matrix(lab, ns); ev, _ = spectrum(M)
            l2 = abs(ev[1]) if len(ev) > 1 else 0.0
            sh = lab.copy(); rng.shuffle(sh)
            Ms = transfer_matrix(sh, ns); evs, _ = spectrum(Ms)
            l2s = abs(evs[1]) if len(evs) > 1 else 0.0
            return l2, l2s
        labels = {
            'x-cell K4 (mu3-cov)': ([cell(xs[d], K) if xs[d] is not None else 0 for d in range(n)], K*K),
            'y-cell K4':           ([min(K-1, ys[d]*K//p) if ys[d] is not None else 0 for d in range(n)], K),
            'y mod 6':             ([ys[d] % 6 if ys[d] is not None else 0 for d in range(n)], 6),
            'y mod 7':             ([ys[d] % 7 if ys[d] is not None else 0 for d in range(n)], 7),
            'y-half (sign)':       ([(1 if (ys[d] is not None and ys[d] < p/2) else 0) for d in range(n)], 2),
            'x-cell x y-half':     ([((cell(xs[d], K) if xs[d] is not None else 0)*2
                                      + (1 if (ys[d] is not None and ys[d] < p/2) else 0)) for d in range(n)], K*K*2),
        }
        row = {'p': p, 'n': n}
        for name, (lab, ns) in labels.items():
            l2, l2s = score(lab, ns)
            row[name] = (l2, l2s, l2/max(l2s, 1e-9))
        rows.append(row)
    return rows


def main():
    print("="*80)
    print("CONSERVATION SPECTRUM v2 -- item #3 (owed: lambda_2 eigenvector mu6-id + general y soft-mode)")
    print("="*80)

    print("\n[a] Is the x-cell lambda_2 eigenvector the mu_3(=mu_6 on x) covariant charge?")
    print("    A = sum_x phi(beta x)conj(phi(x))/sum|phi|^2 ;  |A|~1 & arg~+-120deg => nontrivial-mu_3 mode")
    for lo, hi in [(400, 700), (1000, 1400), (2500, 3000)]:
        p = next(q for q in range(lo, hi) if isprime(q) and q % 3 == 1 and isprime(curve_points_order(q)))
        res = test_a_eigenvector_mu3(p)
        print("   p=%d" % p)
        for tag, (l, aA, arg) in res.items():
            verdict = ""
            if tag == 'l2':
                if aA > 0.6 and abs(abs(arg)-120) < 30:
                    verdict = "  => NONTRIVIAL-mu3 covariant (attribution CONFIRMED)"
                elif aA > 0.6 and abs(arg) < 30:
                    verdict = "  => mu3-TRIVIAL (NOT the mu3 charge)"
                else:
                    verdict = "  => neither clean (|A| low: not a pure mu3 mode)"
            print("      %-16s |lambda|=%.3f  |A|=%.3f  arg(A)=%+.0fdeg%s" % (tag, l, aA, arg, verdict))

    print("\n[b] General y-readout soft-mode: transfer |lambda_2| real/shuffle across p")
    print("    (thermal = real/shuffle -> 1, decaying; a persistent >1 = a metastable soft mode)")
    p_list = []
    for lo, hi in [(400, 700), (1000, 1400), (2500, 3000)]:
        p_list.append(next(q for q in range(lo, hi) if isprime(q) and q % 3 == 1 and isprime(curve_points_order(q))))
    rows = test_b_general_y(p_list)
    labelnames = ['x-cell K4 (mu3-cov)', 'y-cell K4', 'y mod 6', 'y mod 7', 'y-half (sign)', 'x-cell x y-half']
    hdr = "   %-22s" % "label" + "".join("  p=%-5d" % r['p'] for r in rows)
    print(hdr + "   (real/shuffle)")
    for name in labelnames:
        cells = "".join("  %5.2f " % r[name][2] for r in rows)
        print("   %-22s%s" % (name, cells))
    print("\n   (values are real|lam2|/shuffle|lam2|; -> 1.0 across p = thermal/no soft mode)")

    print("\n[done]")


if __name__ == '__main__':
    main()
