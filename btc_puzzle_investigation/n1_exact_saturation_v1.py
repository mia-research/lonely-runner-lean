#!/usr/bin/env python3
"""
n1_exact_saturation_v1.py -- N1: is the 1/2 saturation EXACT?

EXPLORATORY / DERIVATION CHECK, not a confirmatory drill.  There is no statistic, no null and no
p-value here: the script asks whether an exactly-defined quantity is an integer.  Any INFERENCE about
N1's mechanism requires the pre-registration (PREREG_N1_eigenvalue_starvation_v1.md governs that).

OBJECT (as defined in that prereg, section 0a):
    V(a) = sum_{d=1}^{n-1} chi2(y_{[d]G}) e_n(a d),   |V(a)| <= 4 sqrt(p)   [Kummer sheaf, #R = 4]

MOTIVATION.  The ledger records max|V|/(4 sqrt p) -> 0.470 ... 0.500 with "tightness of that
convergence a datum in its own right ... points at something exact rather than statistical."
If A_new is supersingular then the Frobenius eigenvalues on the relevant H^1 are sqrt(p)*zeta with
zeta roots of unity, so V(a)/sqrt(p) = -sum zeta_i is an ALGEBRAIC INTEGER; combined with the M4 real
structure (V real at p=1 mod 4, purely imaginary at p=3 mod 4) the quantity

    Q(a) := |V(a)|^2 / p

is then forced to be a RATIONAL INTEGER, and "2 of 4 eigenvalues" says exactly  max_a Q(a) = 4
(not 16).  That is a yes/no question about an integer, not a saturation ratio.

Also reported for contrast: the ADDITIVE readouts U(a,b,c) = sum_d e_p(b x_d + c y_d) e_n(a d)
(ceiling 4 sqrt p for c != 0, 3 sqrt p for c = 0) which the ledger says saturate 0.876 / 0.909.
"""
import sys
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords


def chi2(u, p):
    if u % p == 0:
        return 0
    return 1 if pow(u % p, (p - 1) // 2, p) == 1 else -1


def spectrum(vals, n):
    """|V(a)|^2 for a = 1..n-1 from the length-n sequence (index d = 0 unused / set 0)."""
    F = np.fft.fft(np.asarray(vals, dtype=complex))
    return (np.abs(F) ** 2)[1:]


def analyse(p, n, G, label, seq):
    P = spectrum(seq, n)
    Q = P / p
    i = int(np.argmax(Q))
    qmax = float(Q[i])
    near = round(qmax)
    # how integral is the whole spectrum?
    dev = np.abs(Q - np.round(Q))
    frac_int = float((dev < 1e-6).mean())
    return dict(label=label, qmax=qmax, near=near, dev_max=abs(qmax - near),
                frac_int=frac_int, med_dev=float(np.median(dev)),
                sat4=qmax ** 0.5 / 4.0, sat3=qmax ** 0.5 / 3.0)


def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    print("=" * 100)
    print("N1 -- is the 1/2 saturation EXACT?   Q(a) = |V(a)|^2 / p ;  '2 of 4' <=> max_a Q = 4")
    print("=" * 100)
    print("%-6s %-4s %-6s %-10s %14s %8s %10s %9s %9s" %
          ("p", "p%4", "n", "readout", "max Q=|V|^2/p", "nearest", "|dev|", "sat/4rp", "%Q integral"))
    seen = set()
    lo_cur = lo
    while lo_cur < hi:
        r = prime_order_curve(lo_cur, min(lo_cur * 2, hi))
        if not r:
            lo_cur = min(lo_cur * 2, hi)
            continue
        p, n, G = r
        if p in seen:
            lo_cur = p + 1
            continue
        seen.add(p)
        xs, ys = group_coords(G, p, n, 0)

        cy = [0] * n
        for d in range(1, n):
            cy[d] = chi2(ys[d], p)
        rows = [analyse(p, n, G, "chi2(y)", cy)]

        cx = [0] * n
        for d in range(1, n):
            cx[d] = chi2(xs[d], p)
        rows.append(analyse(p, n, G, "chi2(x)", cx))

        # additive contrast readouts, best over a small (b,c) sample
        best_u = None
        best_bx = None
        for b in (1, 2, 3):
            for c in (0, 1, 2):
                s = [0] * n
                for d in range(1, n):
                    s[d] = np.exp(2j * np.pi * ((b * xs[d] + c * ys[d]) % p) / p)
                lab = "e_p(%dx+%dy)" % (b, c)
                a = analyse(p, n, G, lab, s)
                if c == 0:
                    if best_bx is None or a['qmax'] > best_bx['qmax']:
                        best_bx = a
                else:
                    if best_u is None or a['qmax'] > best_u['qmax']:
                        best_u = a
        rows += [best_u, best_bx]

        for a in rows:
            print("%-6d %-4d %-6d %-10s %14.5f %8d %10.2e %9.4f %9.3f" %
                  (p, p % 4, n, a['label'], a['qmax'], a['near'], a['dev_max'],
                   a['sat4'], a['frac_int']))
        print()
        lo_cur = p + 1
    print("N1_EXACT_DONE")


if __name__ == '__main__':
    main()
