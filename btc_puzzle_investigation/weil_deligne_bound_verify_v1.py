#!/usr/bin/env python3
"""
Verify the COMMITTED predictions of weil_deligne_character_bound_v1.md §7. The derivation is the
pre-registration; this only checks it. Falsification: any max/sqrt(p) that EXCEEDS its committed
cohomological constant (beyond the +1/sqrt(p) O-term + float noise) means a derivation step is wrong.

Committed bounds  (max over a!=0, exhaustive/scanned twist):
   additive c!=0  (f=bx+cy, dim H^1_c=4)        : max/sqrt(p) <= 4   (+1/sqrt(p))
   additive c==0  (f=bx,     dim H^1_c=3)        : max/sqrt(p) <= 3   ; and c=0 strictly < c!=0 (y adds)
   chi2 of x      (Kummer, #R=2)                 : max/sqrt(p) <= 2
   chi2 of y      (Kummer, #R=4)                 : max/sqrt(p) <= 4
   degenerate (b,c)=(0,0) complete sum, a!=0     : = 0 exactly (complete character sum)

Signal path exact int (coords, Legendre). Float carve-out: FFT magnitudes = analytic-size character
sums, no key in path (btc CLAUDE.md; same carve-out as t_y_maxbound_v1.py).
"""
import math
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords, legendre

BOUND = dict(add_cne=4, add_c0=3, chi2_x=2, chi2_y=4)


def additive_maxratios(xs, ys, p, n):
    """exhaustive (b,c) scan: (max/sqrt(p) for c==0, for c!=0). FFT over d gives all a at once."""
    xsA = np.array(xs, dtype=np.int64); ysA = np.array(ys, dtype=np.int64); sp = math.sqrt(p)
    m_c0 = 0.0; m_cne = 0.0
    for b in range(p):
        for c in range(p):
            if b == 0 and c == 0:
                continue
            ph = np.exp(2j * np.pi * ((b * xsA + c * ysA) % p) / p); ph[0] = 0.0
            U = np.abs(np.fft.fft(ph)); U[0] = 0.0; mm = float(U.max())
            if c == 0: m_c0 = max(m_c0, mm)
            else:      m_cne = max(m_cne, mm)
    return m_c0 / sp, m_cne / sp


def chi2_maxratio(coord, p, n):
    """max_{a!=0} |sum_{d>=1} chi2(coord_d) e_n(a d)| / sqrt(p)."""
    v = np.array([0] + [legendre(int(coord[d]), p) for d in range(1, n)], dtype=float)
    V = np.abs(np.fft.fft(v)); V[0] = 0.0
    return float(V.max()) / math.sqrt(p)


def degenerate_complete(n):
    """(b,c)=(0,0): COMPLETE sum sum_{d=0}^{n-1} e_n(a d) (O carries e_p(0)=1); = 0 for a!=0."""
    v = np.ones(n, dtype=complex)
    V = np.abs(np.fft.fft(v)); V[0] = 0.0
    return float(V.max())


def main():
    print("=" * 90)
    print("WEIL-DELIGNE BOUND VERIFICATION  (checks committed predictions of the derivation)")
    print("=" * 90)
    print("committed constants:", BOUND, "\n")

    # ---- additive (exhaustive (b,c)) on small prime-order secp curves ----
    print("[A] additive U(a,b,c): max/sqrt(p)  (committed: c!=0 <= 4, c=0 <= 3, and c=0 < c!=0)")
    print("    %-22s %-10s %-10s %-24s %s" % ("p (n)", "c=0 /sp", "c!=0 /sp", "c!=0 <= 4 (+1/sp)?", "y strictly adds?"))
    for lo, hi in [(60, 160), (200, 320), (400, 520)]:
        r = prime_order_curve(lo, hi)
        if not r: continue
        p, n, G = r; xs, ys = group_coords(G, p, n, 0)
        c0, cne = additive_maxratios(xs, ys, p, n)
        ok_bound = cne <= BOUND['add_cne'] + 1.0 / math.sqrt(p) + 1e-9
        ok_c0 = c0 <= BOUND['add_c0'] + 1.0 / math.sqrt(p) + 1e-9
        adds = cne > c0 + 1e-9
        print("    p=%-6d n=%-6d %-10.3f %-10.3f %-24s %s" %
              (p, n, c0, cne, "OK" if (ok_bound and ok_c0) else "*** EXCEEDS ***",
               "yes (dim 3->4)" if adds else "no"))

    # ---- chi2 (new: KS does not cover this) on a range of primes ----
    print("\n[B] chi2-twisted single-coordinate: max/sqrt(p)  (committed: chi2(x) <= 2, chi2(y) <= 4)")
    print("    %-16s %-14s %-14s %s" % ("p (n)", "chi2(x) /sp", "chi2(y) /sp", "within bounds?"))
    for lo, hi in [(60, 160), (200, 320), (400, 520), (700, 820), (1200, 1320), (2000, 2120)]:
        r = prime_order_curve(lo, hi)
        if not r: continue
        p, n, G = r; xs, ys = group_coords(G, p, n, 0)
        rx = chi2_maxratio(xs, p, n); ry = chi2_maxratio(ys, p, n)
        okx = rx <= BOUND['chi2_x'] + 1e-9; oky = ry <= BOUND['chi2_y'] + 1e-9
        print("    p=%-6d n=%-6d %-14.3f %-14.3f %s" %
              (p, n, rx, ry, "OK" if (okx and oky) else "*** EXCEEDS: x=%s y=%s ***" % (okx, oky)))

    # ---- degenerate ----
    print("\n[C] degenerate (b,c)=(0,0), complete sum, a!=0  (committed: = 0 exactly)")
    for lo, hi in [(200, 320), (700, 820)]:
        r = prime_order_curve(lo, hi)
        if not r: continue
        p, n, G = r
        d = degenerate_complete(n)
        print("    p=%-6d n=%-6d  max_{a!=0}|sum e_n(ad)| = %.2e  (%s)" %
              (p, n, d, "= 0 OK" if d < 1e-6 else "*** NONZERO ***"))

    print("\n[done]  Any '*** EXCEEDS ***' => a cohomology step is wrong; investigate before claiming.")


if __name__ == "__main__":
    main()
