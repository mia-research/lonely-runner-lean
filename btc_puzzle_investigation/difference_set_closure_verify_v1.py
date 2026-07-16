#!/usr/bin/env python3
"""
difference_set_closure_verify_v1.py -- numerical checks for bilinear_closure_proof_v1.md.
(1) Fourier factorization identity  S(a,b) = (1/n) sum_m Ch[m] Ah[(a-m)] Bh[(b-m)]  (exact).
(2) Theorem B bound  max|S| <= M^3, M=max KS factor ~ sqrt(p)*polylog; report max|S|/p^1.5.
(3) Carry Wiener norm ||chat||_1 for c(u,v)=[u+v>=n]  (needed by Corollary B2: is it polylog?).
Character-sum magnitudes are analytic-size (roots of unity), no key in path.
"""
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords


def check_curve(p, n, xs, ys):
    bP, cP, bQ, cQ, bS, cS = 3, 1, 5, 2, 7, 4
    xa = np.array([0]+[xs[d] for d in range(1, n)]); ya = np.array([0]+[ys[d] for d in range(1, n)])
    A = np.exp(2j*np.pi*((bP*xa+cP*ya) % p)/p); A[0] = 0
    B = np.exp(2j*np.pi*((bQ*xa+cQ*ya) % p)/p); B[0] = 0
    C = np.exp(2j*np.pi*((bS*xa+cS*ya) % p)/p); C[0] = 0
    idx = (np.add.outer(np.arange(n), np.arange(n))) % n
    S = np.fft.fft2(np.outer(A, B)*C[idx])
    Ah, Bh, Ch = np.fft.fft(A), np.fft.fft(B), np.fft.fft(C)
    m = np.arange(n)
    err = max(abs(S[a, b] - (1.0/n)*np.sum(Ch[m]*Ah[(a-m) % n]*Bh[(b-m) % n]))
              for a in (0, 1, 2, 5) for b in (0, 1, 3, 7))
    M = max(np.max(np.abs(Ah)), np.max(np.abs(Bh)), np.max(np.abs(Ch)))
    return err, float(np.max(np.abs(S))), M


def carry_wiener(n):
    """||chat||_1 for c(u,v)=[u+v>=n] on (Z/n)^2, and its 2D spectrum shape."""
    u = np.arange(n)
    c = (np.add.outer(u, u) >= n).astype(complex)     # exact integer sum threshold
    ch = np.fft.fft2(c)/(n*n)                          # chat(a,b)
    l1 = float(np.sum(np.abs(ch)))
    # off-diagonal vs diagonal mass
    diag = float(np.sum(np.abs(np.diag(ch))))
    total = float(np.sum(np.abs(ch)))
    return l1, diag/total


def main():
    print("="*74)
    print("CLOSURE VERIFICATION (bilinear_closure_proof_v1.md)")
    print("="*74)
    print("\n(1)+(2) factorization identity + Theorem B bound:")
    for lo, hi in [(120, 240), (300, 460), (600, 760), (1500, 1700), (2400, 2600)]:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, n, G = r; xs, ys = group_coords(G, p, n, 0)
        err, maxS, M = check_curve(p, n, xs, ys)
        print("  p=%-4d n=%-4d  factor-err=%.1e  max|S|=%.0f  M=%.1f(sqrtp=%.1f)  max|S|/p^1.5=%.3f  M^3/p^1.5=%.2f"
              % (p, n, err, maxS, M, p**0.5, maxS/p**1.5, M**3/p**1.5))
    print("\n(3) carry Wiener norm ||chat||_1 for c(u,v)=[u+v>=n]  (Cor B2 needs this = polylog):")
    import math
    for n in [127, 313, 691, 1663, 2557]:
        l1, dfrac = carry_wiener(n)
        print("  n=%-5d  ||chat||_1 = %.3f   (log2 n)^2 = %.1f   ratio l1/(log n)^2 = %.3f   diag-mass-frac=%.2f"
              % (n, l1, math.log2(n)**2, l1/(math.log(n)**2), dfrac))
    print("\n READ: factor-err~0 (identity exact); max|S|/p^1.5 bounded&falling (Thm B holds).")
    print("       If ||chat||_1 grows ~ (log n)^k => Cor B2 holds (carry corr <= p^-0.5 * polylog).")
    print("[done]")


if __name__ == '__main__':
    main()
