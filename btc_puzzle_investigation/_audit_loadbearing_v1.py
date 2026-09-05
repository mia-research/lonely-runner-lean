#!/usr/bin/env python3
"""
_audit_loadbearing_v1.py -- decidable audit of the two load-bearing claims. Float only for |.|.

CLAIM 1 (KS U-bound, [PROVED given KS], the theorem that extends to secp and closes single-point
leakage):   max_{a, (b,c)!=(0,0)} |U(a,b,c)|  <=  4 sqrt(p) + 1,   and  max_a|T(a,b)|=|U(a,b,0)| <= 3 sqrt(p).
  U(a,b,c) = sum_{d in Z/n} e_p(b x_d + c y_d) e_n(a d).
  DECIDABLE: compute the exact max over ALL (a,b,c) at small p via FFT-in-a; check <= 4 sqrt(p)+1.
  If the measured max EXCEEDS the bound, the load-bearing theorem is contradicted at that p.

CLAIM 2 (the 0.93 joint shadow): the aligned readout Fhat(b,c)=conj(U(a0,b,c))/|U| gives
  |Corr(a0)|/||Fhat||_2 ~ 0.93 (joint x,y) vs ~0.34 (x only). DECIDABLE: recompute at a few p.

Curve: y^2 = x^3 + 7 over F_p, p=1 mod6, n=#E prime, G a generator, P_d=[d]G.
"""
import sys, cmath, math
import numpy as np
from sympy import isprime
from sympy.ntheory.residue_ntheory import sqrt_mod

def curve(p):
    def add(A, B):
        if A is None: return B
        if B is None: return A
        x1, y1 = A; x2, y2 = B
        if x1 == x2:
            if (y1 + y2) % p == 0: return None
            l = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
        else: l = (y2 - y1) * pow(x2 - x1, -1, p) % p
        x3 = (l * l - x1 - x2) % p
        return (x3, (l * (x1 - x3) - y1) % p)
    G = None
    for x in range(1, p):
        r = (x * x * x + 7) % p
        if pow(r, (p - 1) // 2, p) == 1:
            y = int(sqrt_mod(r, p));  G = (x, y); break
    pts = [None]; cur = G                 # pts[0] = O placeholder
    while cur is not None:
        pts.append(cur); cur = add(cur, G)
    n = len(pts)                          # = #E: pts[1..n-1]=[1]G..[n-1]G, pts[0]=O
    return G, pts, n

def audit_KS(plist):
    print("=== CLAIM 1: KS U-bound  max|U| <= 4 sqrt(p)+1  (and T: <= 3 sqrt(p)) ===")
    print(f"  {'p':>5} {'n':>5} {'max|U| c!=0':>12} {'4sqrt(p)+1':>11} {'ok':>4} {'max|T|(c=0)':>12} {'3sqrt(p)':>9} {'ok':>4}")
    worst_ratio = 0
    for p in plist:
        if p % 6 != 1 or not isprime(p): continue
        G, pts, n = curve(p)
        if not isprime(n): continue
        d_idx = np.arange(1, n)                          # d = 1..n-1 (d=0 is O, excluded)
        xs = np.array([pts[d][0] for d in d_idx])
        ys = np.array([pts[d][1] for d in d_idx])
        wp = 2 * math.pi / p
        maxU = 0.0; maxT = 0.0
        for b in range(p):
            for c in range(p):
                if b == 0 and c == 0: continue
                g = np.zeros(n, dtype=complex)
                g[1:] = np.exp(1j * wp * ((b * xs + c * ys) % p))   # g[0]=0 (O); FFT over d=0..n-1
                U = np.abs(np.fft.fft(g))                           # |U(a,b,c)| over all a
                m = U.max()
                if c == 0: maxT = max(maxT, m)
                else: maxU = max(maxU, m)
        bnd = 4 * math.sqrt(p) + 1; bndT = 3 * math.sqrt(p)
        okU = maxU <= bnd + 1e-6; okT = maxT <= bndT + 1e-6
        worst_ratio = max(worst_ratio, maxU / bnd)
        print(f"  {p:>5} {n:>5} {maxU:>12.3f} {bnd:>11.3f} {str(okU):>4} {maxT:>12.3f} {bndT:>9.3f} {str(okT):>4}")
    print(f"  worst max|U|/(4sqrt(p)+1) = {worst_ratio:.3f}  ({'BOUND HOLDS' if worst_ratio<=1 else 'BOUND VIOLATED'})")

def audit_shadow(plist):
    print("\n=== CLAIM 2: the 0.93 joint (x,y) shadow vs 0.34 (x-only) ===")
    print(f"  {'p':>5} {'n':>5} {'aligned x-only':>14} {'aligned JOINT(x,y)':>18} {'ratio':>6}")
    for p in plist:
        if p % 6 != 1 or not isprime(p): continue
        G, pts, n = curve(p)
        if not isprime(n): continue
        d_idx = np.arange(1, n)
        xs = np.array([pts[d][0] for d in d_idx])
        ys = np.array([pts[d][1] for d in d_idx])
        wp = 2 * math.pi / p; wn = 2 * math.pi / n
        a0 = 1
        phase = np.exp(-1j * wn * a0 * d_idx)            # e_n(-a0 d), d=1..n-1
        # record metric: aligned readout Fhat=conj(U)/|U| over the channel, |Corr(a0)|/||F||.
        # avg_{b,c}|U(a0,b,c)| / sqrt(n): random channel -> ~sqrt(pi)/2 ~ O(1)?; aligned combines them.
        # Reproduce v16's |Corr|/||F||_inf where F=Fhat (|Fhat|=1): Corr(a0)=(1/n) sum_{b,c}|U(a0,b,c)|,
        # ||F||_inf over the d-domain readout = max_d |readout|. Simpler equivalent used in cheap_partial:
        # rho = (avg over channels of |U(a0,b,c)|) / sqrt(n).  x-only: c=0 channels; joint: all (b,c).
        def rho(use_c):
            s = 0.0; cnt = 0
            for b in range(p):
                for c in (range(p) if use_c else [0]):
                    if b == 0 and c == 0: continue
                    g = np.exp(1j * wp * ((b * xs + c * ys) % p))
                    U = np.sum(g * phase)
                    s += abs(U); cnt += 1
            return (s / cnt) / math.sqrt(n)
        rx = rho(False); rj = rho(True)
        print(f"  {p:>5} {n:>5} {rx:>14.3f} {rj:>18.3f} {rj/rx if rx else 0:>6.2f}")
    print("  (record: x-only ~0.34, joint ~0.93, ratio ~2.8. Checking the numbers reproduce.)")

def main():
    ks_p = [61, 67, 103, 151, 211, 307]
    audit_KS(ks_p)
    audit_shadow([163, 211, 433])

if __name__ == '__main__':
    main()
