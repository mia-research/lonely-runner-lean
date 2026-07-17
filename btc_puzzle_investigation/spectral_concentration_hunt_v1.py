#!/usr/bin/env python3
"""
spectral_concentration_hunt_v1.py -- the ONE open door (v14/v31): is there a CHEAP readout F
(computable from curve coordinates, WITHOUT d) whose character spectrum concentrates on a single a0?

Corr_F(a) = (1/n) sum_d F(P_d) e_n(-a d).   Concentration = C(F) := max_{a!=0} |Corr_F(a)| / ||F||_2,
||F||_2 = sqrt((1/n) sum_d |F(P_d)|^2).  By Parseval sum_a|Corr_F|^2=||F||_2^2, so a RANDOM readout
has C ~ sqrt(log n / n) (the FLOOR).  The ALIGNED readout F(P_d)=e_n(a0 d) has C=1 (needs d = DLP).
Closure theorem: bounded-Wiener single-coord readouts have C=O(p^-1/2)=floor.  v15: phase alignment,
not Wiener norm, is the sole axis.  HUNT: does ANY cheap readout beat the floor, and does the best
one's C/floor GROW or DECAY with p?  Grow => a concentration lever (a break); decay/flat => none.

DISCIPLINE:
 * PLANTED control F=e_n(a0 d) (uses d) MUST give C~1 -> validates the detector.
 * random-readout null calibrates the floor.
 * report C/floor and its SCALING across p (one prime proves nothing -- v14's lesson).
 * candidates: cheap coord readouts incl. high-Wiener (chi2/3/6), lift-geometric (sextant/eps/norm),
   the xy odd+mu3 family, Frobenius/CM-derived, and 2-term products (phase-combination hunt).

Character-sum magnitudes are analytic-size (no key in path).
"""
import math, cmath
import numpy as np
from sympy import isprime
from t_y_maxbound_v1 import prime_order_curve, group_coords
from int1_frame_operator_v1 import build

Z3 = cmath.exp(2j*math.pi/3)
Z6 = cmath.exp(2j*math.pi/6)


def legendre_pm(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1

def chi_k(a, p, k, zeta):
    a %= p
    if a == 0:
        return 0j
    e = (p-1)//k
    r = pow(a, e, p)
    # map the k-th root subgroup element to a root of unity by discrete log over a small table
    # (k small: brute a small generator of the order-k subgroup)
    return _chi_table[k].get(r, 0j)

_chi_table = {}
def build_chi_tables(p):
    _chi_table.clear()
    for k in (2, 3, 6):
        e = (p-1)//k
        # find element g of order k
        vals = {}
        # collect the k-th roots of unity in F_p: {a^e}
        seen = {}
        g = 2
        while pow(g, e, p) == 1 or len(set(pow(pow(g, e, p), j, p) for j in range(k))) < k:
            g += 1
        w = pow(g, e, p)
        for j in range(k):
            seen[pow(w, j, p)] = cmath.exp(2j*math.pi*j/k)
        _chi_table[k] = seen


def concentration(Fvals, n):
    """C(F)=max_{a!=0}|Corr_F(a)|/||F||_2 via FFT over d."""
    F = np.asarray(Fvals, dtype=complex).copy(); F[0] = 0.0
    l2 = math.sqrt(float(np.mean(np.abs(F[1:])**2))) or 1e-18
    C = np.fft.fft(F)/n; C[0] = 0.0
    return float(np.max(np.abs(C)))/l2


def readouts(xs, ys, p, n):
    build_chi_tables(p)
    eis, eps = build(p)
    def arr(f):
        return np.array([0.0]+[f(xs[d], ys[d]) for d in range(1, n)], dtype=complex)
    R = {}
    # high-Wiener multiplicative characters (v15: chi2 saturates norm, does NOT leak)
    R['chi2(x)'] = arr(lambda x, y: float(legendre_pm(x, p)))
    R['chi3(x)'] = arr(lambda x, y: _chi_table[3].get(pow(x % p, (p-1)//3, p), 0j) if x % p else 0j)
    R['chi6(x)'] = arr(lambda x, y: _chi_table[6].get(pow(x % p, (p-1)//6, p), 0j) if x % p else 0j)
    R['chi2(y)'] = arr(lambda x, y: float(legendre_pm(y, p)))
    # additive single-freq (KS floor by construction)
    R['e_p(x)'] = arr(lambda x, y: cmath.exp(2j*math.pi*x/p))
    R['e_p(xy)'] = arr(lambda x, y: cmath.exp(2j*math.pi*(x*y % p)/p))
    # lift-geometric
    R['eps(flap)'] = arr(lambda x, y: float(eps(x)))
    # xy odd+mu3 family (this session's positive object)
    R['sign(xy)'] = arr(lambda x, y: 1.0 if (x*y % p) < p/2 else -1.0)
    R['chi3(xy)'] = arr(lambda x, y: _chi_table[3].get(pow((x*y) % p, (p-1)//3, p), 0j) if (x*y) % p else 0j)
    R['s_y'] = arr(lambda x, y: 1.0 if y < p/2 else -1.0)
    # Frobenius/CM: chi6(x)*s_y (odd+mu6 combination), chi3(x)*s_y
    R['chi6(x)*s_y'] = R['chi6(x)']*R['s_y']
    R['chi3(x)*s_y'] = R['chi3(x)']*R['s_y']
    R['chi2(x)*s_y'] = R['chi2(x)']*R['s_y']
    return R


def main():
    print("="*86)
    print("SPECTRAL-CONCENTRATION HUNT -- is a cheap readout's spectrum concentrated? (v14/v31 open door)")
    print("  C(F)=max_a|Corr_F(a)|/||F||_2 ; floor~sqrt(log n/n) ; aligned(needs d)=1 ; growth of C/floor => lever")
    print("="*86)
    primes = []
    for lo, hi in [(200, 400), (500, 700), (900, 1200), (1500, 1800), (2400, 2700), (4000, 4300), (6000, 6300)]:
        r = prime_order_curve(lo, hi)
        if r:
            primes.append(r)
    best_track = {}
    for p, n, G in primes:
        xs, ys = group_coords(G, p, n, 0)
        floor = math.sqrt(math.log(n)/n)
        # planted aligned control (uses d) -- MUST be ~1
        a0 = 1
        aligned = np.array([0.0]+[cmath.exp(2j*math.pi*a0*d/n) for d in range(1, n)], dtype=complex)
        C_aligned = concentration(aligned, n)
        # random null
        rng = np.random.default_rng(p)
        C_rand = concentration(rng.choice([-1.0, 1.0], size=n).astype(complex), n)
        R = readouts(xs, ys, p, n)
        Cs = {name: concentration(F, n) for name, F in R.items()}
        best_name = max(Cs, key=Cs.get); best = Cs[best_name]
        best_track.setdefault('p', []).append(p)
        best_track.setdefault('best', []).append(best/floor)
        top = sorted(Cs.items(), key=lambda t: -t[1])[:3]
        print("\n p=%d n=%d  floor=%.4f  aligned(CTRL)=%.3f (C/floor=%.0f)  random=%.4f (C/floor=%.1f)"
              % (p, n, floor, C_aligned, C_aligned/floor, C_rand, C_rand/floor))
        print("   best cheap: %-14s C=%.4f  C/floor=%.2f   top3: %s"
              % (best_name, best, best/floor, ", ".join("%s=%.2f" % (k, v/floor) for k, v in top)))
    print("\n SCALING of the best cheap readout's C/floor across p (the decisive test):")
    for p, r in zip(best_track['p'], best_track['best']):
        print("   p=%-5d  best C/floor = %.2f" % (p, r))
    print("\n READ: aligned CTRL C/floor ~ sqrt(n/log n) (huge) => detector sees concentration when real.")
    print("       best cheap C/floor FLAT/DECAYING across p => no cheap concentration (door stays shut);")
    print("       GROWING => a concentration lever worth chasing.")
    print("[done]")


if __name__ == '__main__':
    main()
