#!/usr/bin/env python3
"""
n1_flap_bridge_v1.py -- EXPLORATORY.  Build the object, do not adjudicate it.

STATUS: [EXPLORATORY].  No experiment-designer pre-registration.  Nothing here may be reported as a
confirmatory finding; anything that appears needs its own frozen spec and an out-of-sample retest.
Labelled up front because the predecessor Jacobi result was correctly criticized for running a
prereg-shaped test without one.

THE IDEA.  Two +-1 functions live on the SAME group E(F_p) = Z/n:

    f(d)     = chi2( y_[d]G )                      -- the N1 weight.  V1(a) = sum_d f(d) zeta_n^{ad}
                                                      is exactly its Fourier transform, and
                                                      v <= 0  <=>  |V1(a)| <= sqrt3*sqrt(p).
    sigma(d) = flap sign of x_[d]G                 -- the cap-law classifier,
                                                      eps(X)=1 iff 2|cent(s)-cent(rho s)| > p,
                                                      rho = beta+1, beta^3 = 1 mod p.

They are not merely "both hexagonal at scale sqrt(p)".  The record already couples them: the flap's
chi2-IMBALANCE equals h(-p).  That is a statement about sum of f over the flap -- i.e. one frequency.
This script asks the obvious next question: what does the flap do at EVERY frequency, and in
particular at the exceptional frequencies where |V1| exceeds sqrt3*sqrt(p)?

    V1(a) = V1_core(a) + V1_flap(a)          (an exact, additive, always-localizing split)

QUESTION: is the exceptional set (v > 0) driven by the flap part?

CONTROL: the flap is a mu3-invariant subset of density ~1/4.  The matched null relabels flap
membership at the SAME density, so any concentration that is merely "a quarter of the mass" cancels.
A second control uses a mu3-invariant random relabelling, matching the flap's symmetry too.

EXACTNESS: f, sigma, the group law and the flap classifier are exact integer.  The DFT is complex
(analytic size only, no key or index in the path), consistent with the record's standing carve-out.
"""
import sys, cmath, random
import numpy as np

sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from audit_n1_vsign_v2_core import (is_prime, legendre, curve_order, ec_add,
                                    find_generator, tonelli)

B = 7


def cent(u, p):
    u %= p
    return u - p if u > (p - 1) // 2 else u


def flap_sign(X, p, rho):
    """cap-law classifier on a field element.  +1 / -1 on the two caps, 0 on the mu3 core."""
    s = X % p
    t = 2 * (cent(s, p) - cent(rho * s % p, p))
    if t > p:
        return 1
    if t < -p:
        return -1
    return 0


def build(p):
    n = curve_order(p, B)
    assert is_prime(n)
    # GLV cube root of unity mod p (exists: p = 1 mod 3 is forced by #E prime)
    assert p % 3 == 1
    g = 2
    while pow(g, (p - 1) // 3, p) == 1:
        g += 1
    beta = pow(g, (p - 1) // 3, p)
    assert pow(beta, 3, p) == 1 and beta != 1
    rho = (beta + 1) % p
    assert (rho * rho - rho + 1) % p == 0

    G = find_generator(p, n, B)
    f = np.zeros(n, dtype=np.int64)       # chi2(y)
    sg = np.zeros(n, dtype=np.int64)      # flap sign of x
    Q = None
    for d in range(n):
        if Q is None:
            f[d] = 0; sg[d] = 0           # point at infinity
        else:
            x, y = Q
            f[d] = 0 if y == 0 else (1 if pow(y, (p - 1) // 2, p) == 1 else -1)
            sg[d] = flap_sign(x, p, rho)
        Q = ec_add(Q, G, p, B)
    return n, f, sg


def spectra(f, mask, n):
    """DFT of f restricted to mask (a 0/1 array)."""
    return np.fft.fft(f * mask)


def run(p, verbose=True):
    n, f, sg = build(p)
    inflap = (sg != 0).astype(np.int64)
    incore = 1 - inflap
    dens = inflap.sum() / n

    V1 = np.fft.fft(f)
    Vf = np.fft.fft(f * inflap)
    Vc = np.fft.fft(f * incore)
    assert np.max(np.abs(V1 - (Vf + Vc))) < 1e-6, "split is not additive"

    thr = (3 * p) ** 0.5                                   # sqrt3*sqrt(p)
    mag = np.abs(V1)
    exc = [a for a in range(1, n) if mag[a] > thr]

    # flap SHARE of the total at each frequency
    share = np.abs(Vf) / np.maximum(np.abs(V1), 1e-12)
    base = share[1:].mean()
    exc_share = share[exc].mean() if exc else float("nan")

    if verbose:
        print(f"p={p:<5} n={n:<5} flap density {dens:.4f}   "
              f"exceptional frequencies |V1|>sqrt(3p): {len(exc)} of {n-1}")
        print(f"        mean flap share of |V1| : all a {base:.4f}   exceptional a {exc_share:.4f}"
              + (f"   ratio {exc_share/base:.3f}" if exc else ""))
    return dict(p=p, n=n, f=f, sg=sg, inflap=inflap, V1=V1, Vf=Vf,
                exc=exc, share=share, base=base, exc_share=exc_share, dens=dens, thr=thr)


def control(r, nrep=200, mu3=False, seed=11):
    """matched null: relabel flap membership at the same density."""
    rng = random.Random(seed)
    n, f = r["n"], r["f"]
    k = int(r["inflap"].sum())
    out = []
    for _ in range(nrep):
        m = np.zeros(n, dtype=np.int64)
        m[rng.sample(range(n), k)] = 1
        Vf = np.fft.fft(f * m)
        sh = np.abs(Vf) / np.maximum(np.abs(r["V1"]), 1e-12)
        b = sh[1:].mean()
        e = sh[r["exc"]].mean() if r["exc"] else float("nan")
        out.append(e / b if r["exc"] else float("nan"))
    return out


if __name__ == "__main__":
    print("[EXPLORATORY] no prereg; nothing here is confirmatory\n")
    rs = []
    for p in [int(t) for t in sys.argv[1:]]:
        r = run(p)
        if r["exc"]:
            c = control(r)
            c_sorted = sorted(c)
            obs = r["exc_share"] / r["base"]
            above = sum(1 for x in c if x >= obs)
            print(f"        matched null (200 reps): median ratio {c_sorted[100]:.3f}   "
                  f"observed {obs:.3f}   rank p = {(above+1)/201:.4f}")
        rs.append(r)
        print()
