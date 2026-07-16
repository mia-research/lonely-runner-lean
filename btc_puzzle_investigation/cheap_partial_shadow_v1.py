#!/usr/bin/env python3
"""
cheap_partial_shadow_v1.py -- Item #4: is there a CHEAP (DLP-free) readout capturing a FRACTION
of the aligned joint (x,y) shadow (v16: |Corr|/||F||_inf = 0.93, but F needs U = the DLP)?

CLOSURE (given item #2): a cheap readout is a point-function F(P), F(P)=sum_{b,c} Fhat(b,c) e_p(bx+cy).
  Corr_F(a) = (1/n) sum_d F(P_d) e_n(-a d) = sum_{b,c} Fhat(b,c) U(a,b,c) / n.
Item #2 (v21): |U(a,b,c)| <= C sqrt(p) polylog UNIFORMLY over (b,c). Hence for bounded-2D-Wiener F
(||Fhat||_1 = p^{o(1)}):  |Corr_F(a)| <= ||Fhat||_1 * C sqrt(p) polylog / n = p^{-1/2+o(1)}  -> the
NOISE FLOOR.  So NO cheap single-key readout of (x,y) captures a constant fraction of the 0.93
shadow: the closure theorem extends from x-readouts to joint (x,y) readouts.  [PROVED given KS +
bounded 2D-Wiener].  This script CONFIRMS it: a battery of cheap readouts sits at the random floor,
far below the aligned reference, and the best cheap readout -> 0 as p grows.

Metric (normalization-free correlation coefficient with the leaking character):
  rho(F) = max_{a!=0} |Corr_F(a)| / ||F||_2 ,   ||F||_2 = sqrt((1/n) sum_d |F(P_d)|^2).
  rho=1  <=> F perfectly aligned to a character e_n(a d)  (=the perfect leak, needs d).
  random / cheap F: rho ~ sqrt(log n)/sqrt(n) -> 0  (the noise floor).

FLOAT CARVE-OUT: analytic-size character-sum magnitudes; no key in the signal path (same carve-out
as glv_closure_verification / t_y_maxbound).
"""
import math
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords


def corr_rho(Fd, n):
    """max_{a!=0} |Corr_F(a)| / ||F||_2, over a. Fd: complex array length n (index 0 unused)."""
    F = np.asarray(Fd, dtype=complex).copy()
    F[0] = 0.0
    l2 = math.sqrt(float(np.mean(np.abs(F[1:])**2))) or 1e-12
    C = np.fft.fft(F) / n            # Corr_F(a) for all a
    C[0] = 0.0
    return float(np.max(np.abs(C))) / l2


def cheap_readouts(xs, ys, p, n):
    """A diverse battery of CHEAP (DLP-free) point-readouts F(P_d)."""
    def arr(f):
        return np.array([0.0] + [f(xs[d], ys[d]) for d in range(1, n)], dtype=complex)
    R = {
        'y-sign(half)':    arr(lambda x, y: 1.0 if y < p/2 else -1.0),
        'y mod 2':         arr(lambda x, y: 1.0 if y % 2 else -1.0),
        'y mod 6':         arr(lambda x, y: np.exp(2j*math.pi*(y % 6)/6)),
        'x mod 6':         arr(lambda x, y: np.exp(2j*math.pi*(x % 6)/6)),
        'x-half':          arr(lambda x, y: 1.0 if x < p/2 else -1.0),
        'e_p(x)':          arr(lambda x, y: np.exp(2j*math.pi*x/p)),
        'e_p(y)':          arr(lambda x, y: np.exp(2j*math.pi*y/p)),
        'e_p(x+y)':        arr(lambda x, y: np.exp(2j*math.pi*((x+y) % p)/p)),
        'e_p(x-y)':        arr(lambda x, y: np.exp(2j*math.pi*((x-y) % p)/p)),
        'sign(xy)':        arr(lambda x, y: 1.0 if (x*y % p) < p/2 else -1.0),
        '(x*y) mod 2':     arr(lambda x, y: 1.0 if (x*y) % 2 else -1.0),
        'y-half * x-parity': arr(lambda x, y: (1.0 if y < p/2 else -1.0)*(1.0 if x % 2 else -1.0)),
    }
    return R


def aligned_reference(xs, ys, p, n, a0=1):
    """The v16 aligned joint readout rho (needs U): Fhat(b,c)=conj(U(a0,b,c))/|U|. Full (b,c), small p."""
    xsA = np.array([0]+[xs[d] for d in range(1, n)], dtype=np.int64)
    ysA = np.array([0]+[ys[d] for d in range(1, n)], dtype=np.int64)
    # build U(a0,b,c) for all (b,c)
    Ubc = np.zeros((p, p), dtype=complex)
    for b in range(p):
        for c in range(p):
            ph = np.exp(2j*math.pi*((b*xsA + c*ysA) % p)/p); ph[0] = 0.0
            Ubc[b, c] = np.fft.fft(ph)[a0]
    nz = np.abs(Ubc) > 1e-9
    Fh = np.zeros_like(Ubc); Fh[nz] = np.conj(Ubc[nz])/np.abs(Ubc[nz]); Fh[0, 0] = 0
    # rho of the aligned readout: |Corr(a0)| / ||F||_2 in point space
    corr = abs(np.sum(Fh*Ubc))/n          # = |Corr_Faligned(a0)|
    l2 = math.sqrt(float(np.sum(np.abs(Fh)**2)))/math.sqrt(n)   # ||F||_2 in point space
    return corr/max(l2, 1e-12)


def main():
    print("="*78)
    print("CHEAP PARTIAL of the joint (x,y) shadow -- item #4")
    print("rho(F)=max_a|Corr_F(a)|/||F||_2 ;  cheap/random -> ~sqrt(log n)/sqrt(n) (floor); aligned=O(1) needs U")
    print("="*78)

    print("\n[battery] cheap (DLP-free) readouts vs random floor, scaling across p")
    prem = []
    for lo, hi in [(120, 240), (400, 700), (1000, 1400), (2000, 2600)]:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, n, G = r
        xs, ys = group_coords(G, p, n, 0)
        R = cheap_readouts(xs, ys, p, n)
        rng = np.random.default_rng(p)
        rand = rng.choice([-1.0, 1.0], size=n).astype(complex); rand[0] = 0
        floor = corr_rho(rand, n)
        best_name, best = max(((nm, corr_rho(F, n)) for nm, F in R.items()), key=lambda t: t[1])
        allrho = {nm: corr_rho(F, n) for nm, F in R.items()}
        prem.append((p, n, floor, best_name, best, allrho))
        top3 = sorted(allrho.items(), key=lambda t: -t[1])[:3]
        print("  p=%-4d n=%-4d  random-floor rho=%.4f   best cheap: %s=%.4f   (top3: %s)"
              % (p, n, floor, best_name, best, ", ".join("%s=%.3f" % (k, v) for k, v in top3)))

    print("\n[reference] the ALIGNED joint readout (needs U = the DLP), small p")
    for lo, hi in [(120, 240), (150, 260)]:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, n, G = r
        if p > 260:
            continue
        xs, ys = group_coords(G, p, n, 0)
        rho_al = aligned_reference(xs, ys, p, n)
        # cheap best + floor at this p for the contrast line
        R = cheap_readouts(xs, ys, p, n)
        best = max(corr_rho(F, n) for F in R.values())
        rng = np.random.default_rng(p); rand = rng.choice([-1.0, 1.0], size=n).astype(complex); rand[0]=0
        print("  p=%-4d  ALIGNED(needs U) rho=%.3f   vs   best cheap rho=%.4f   random-floor=%.4f"
              % (p, rho_al, best, corr_rho(rand, n)))

    print("\n[scaling] does the best cheap readout decay to the floor?  (rho * sqrt(n/ln n))")
    for (p, n, floor, bn, best, allrho) in prem:
        sc = best * math.sqrt(n/math.log(n))
        print("  p=%-4d  best-cheap rho=%.4f  floor=%.4f  best/floor=%.2f  rho*sqrt(n/ln n)=%.2f"
              % (p, best, floor, best/max(floor, 1e-9), sc))

    print("\n[done]")


if __name__ == '__main__':
    main()
