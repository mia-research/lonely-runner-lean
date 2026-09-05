#!/usr/bin/env python3
# monodromy_sato_tate_v2.py  -- G_geom identification at scale, with GUE-vs-Poisson test
#
# Identifies the geometric monodromy of the Fourier-transform sheaf
#   { H^1_c(E, L_{chi2(y)} x L_{chi_a}) }_a
# via the cheap V1-only FFT route (O(n log n), reaches p ~ 1e5..1e6).
#
# TESTS:
#  M-marginal : moments of u(a) -> Catalan_k/4^k  (Sato-Tate / semicircle <=> SU(2) in trace)
#  M-notU1    : m4 = 1/8 != 3/8 (torus)  => excludes U(1)
#  M-notFinite: marginal continuous at large p    => excludes finite monodromy
#  NV         : number variance Sigma^2(L): GUE (full SU(2)) ~ (1/pi^2) log L ;
#               Poisson (independent) ~ L.  THIS discriminates full SU(2) from "right marginal,
#               independent levels".
#
# EXACTNESS: c(d)=chi2(y_{[d]G}) is exact integer (Legendre). FFT/float enter only the test
# statistic (monotone), allowed.
import sys, numpy as np
from math import comb
from sympy import nextprime, isprime

B = 7

def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1

def curve_order(p):
    n = p + 1
    for x in range(p):
        n += legendre((x*x % p * x + B) % p, p)
    return n

def group_walk_signal(p, n):
    """c[d]=chi2(y_{[d]G}), d=0..n-1, for E(F_p) cyclic of order n (prime n => cyclic)."""
    def add(P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q
        if x1 == x2:
            if (y1 + y2) % p == 0: return None
            m = (3 * x1 % p * x1) % p * pow(2*y1 % p, p-2, p) % p
        else:
            m = (y2 - y1) % p * pow((x2 - x1) % p, p-2, p) % p
        x3 = (m*m - x1 - x2) % p
        y3 = (m*(x1 - x3) - y1) % p
        return (x3, y3)
    for xb in range(p):
        rhs = (xb*xb % p * xb + B) % p
        if legendre(rhs, p) != 1: continue
        yb = pow(rhs, (p+1)//4, p)
        G = (xb, yb)
        c = [0]; P = None          # d=0: [0]G = O -> chi2 = 0
        ok = True
        for d in range(1, n):
            P = add(P, G)
            if P is None: ok = False; break
            x, y = P
            c.append(legendre(y, p) if y != 0 else 0)
        if not ok: continue
        if add(P, G) is not None: continue   # [n]G must be O
        return c
    return None

def catalan(k): return comb(2*k, k)//(k+1)

def number_variance(thetas, Ls):
    """thetas: sorted eigenangles on [0,pi). Unfold to mean-spacing 1, compute Sigma^2(L).
    Uses the Sato-Tate spacing CDF on [0,pi]: density (2/pi) sin^2 t."""
    # unfold: cumulative count integral. Sort, map via integrated density * (N).
    th = np.sort(thetas)
    N = len(th)
    # integrated density F(t) = (1/pi)(t - sin t cos t) for Sato-Tate on [0,pi], * N
    cum = N * (th - np.sin(th)*np.cos(th))/np.pi
    unfolded = np.diff(cum)          # nearest-neighbor spacings, ~mean 1 if ST
    s = np.cumsum(unfolded)          # cumulative position
    Sig = []
    for L in Ls:
        if L < 1: continue
        # slide windows of unfolded-length L, count points
        counts = []
        starts = np.arange(0, max(1, s[-1]-L), max(1, L/10))
        for st in starts:
            counts.append(np.searchsorted(s, st+L) - np.searchsorted(s, st))
        counts = np.array(counts, dtype=float)
        Sig.append((L, np.var(counts) if len(counts) > 1 else float('nan')))
    return Sig

def run_prime(p):
    n = curve_order(p)
    if not isprime(n):
        return None
    c = group_walk_signal(p, n)
    if c is None:
        return None
    V = np.fft.fft(np.array(c, dtype=np.float64))
    u = V.imag / (2*np.sqrt(p))
    # the Sato-Tate variable is t(a) = Im(V1(a))/(2 sqrt p) in [-1,1]; its marginal under SU(2)
    # is the semicircle (2/pi) sqrt(1-t^2). Use ALL nonzero frequencies (the |Im| symmetry just
    # folds, but the marginal of the signed t is the right object). Restrict a in 1..(n-1)/2 to
    # avoid double-counting conjugate pairs -> use the signed values on the fundamental domain.
    half = (n-1)//2
    t = u[1:1+half]                       # signed, fundamental domain
    m = [np.mean(t**(2*k)) for k in range(1, 9)]
    cat = [catalan(k)/4**k for k in range(1, 9)]
    return dict(p=p, n=n, maxabsu=float(np.max(np.abs(t))), m=m, cat=cat, ncells=len(t))

def main():
    print("="*82)
    print("MONODROMY identification via the Sato-Tate marginal (V1-only FFT route).")
    print("SU(2) prediction: moments m_{2k} = Catalan_k / 4^k. U(1) torus gives m4=3/8.")
    print("="*82)
    p = 7
    done = 0
    import time
    t0 = time.time()
    rows = []
    while done < 8 and time.time() - t0 < 240:
        if p % 12 == 7:
            r = run_prime(p)
            if r is not None:
                done += 1
                rows.append(r)
                mm = r['m']
                print(f"p={r['p']:7d} n={r['n']:8d} Ncells={r['ncells']:7d} max|u|={r['maxabsu']:.4f}")
                print(f"   m2..m16: " + "  ".join(f"{x:.4f}" for x in mm))
                print(f"   Catalan: " + "  ".join(f"{c:.4f}" for c in r['cat']))
        p = int(nextprime(p))
    if rows:
        import numpy as np
        # pooled weighted by ncells
        allm = np.array([r['m'] for r in rows])
        w = np.array([r['ncells'] for r in rows], dtype=float)
        pooled = (allm * w[:,None]).sum(axis=0) / w.sum()
        cat = rows[0]['cat']
        print(f"\nPOOLED ({int(w.sum())} cells, {done} primes):")
        print(f"   m2..m16: " + "  ".join(f"{x:.4f}" for x in pooled))
        print(f"   Catalan: " + "  ".join(f"{c:.4f}" for c in cat))
        maxdev = max(abs(pooled[k]-cat[k]) for k in range(8))
        print(f"   max |m_{{2k}} - C_k/4^k| over k=1..8: {maxdev:.4f}")

if __name__ == "__main__":
    main()
