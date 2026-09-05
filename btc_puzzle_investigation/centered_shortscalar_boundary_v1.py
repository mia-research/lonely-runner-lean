#!/usr/bin/env python3
"""centered_shortscalar_boundary_v1.py -- the CENTERED short-scalar statistic at the GLV boundaries.

The earlier harness died because S = sum r_i N_i is dominated by N_0 * T, and T = sum r_i is
permutation-invariant, so the test had no power (a 100% plant read p = 1.0).  The repair is to strip
that mass and keep only the Babai rounding residual:

    delta_i = N_i - mean(N over the interval)          (the centred lattice footprint)
    S_cent  = sum_i r_i * delta_i,      r_i = chi_2(x_{[d_0+i]G})

S_cent has zero expectation under a permutation of r and is NOT dominated by any invariant term.

WHERE.  At a GLV Voronoi boundary the Babai coefficient c_2 ticks over, (k1,k2) jumps by a lattice
vector, and delta acquires a STEP -- the only place in the scalar line where the footprint does
anything.  Boundaries are located EXACTLY (integer arithmetic): c_2(d) = round(-d*B1/N) increments
where -d*B1 + N//2 crosses a multiple of N.  Spacing ~ N/|B1| ~ 2^129, so a usable sample needs a
scan across [2^128, 2^136); each interval is still at the 2^128-2^136 scale.

ARMS
  BOUNDARY : intervals centred on an exact c_2 boundary.
  CONTROL  : intervals at random offsets containing NO boundary (matched width, matched scale).
NULL       : permutation of r within the interval (preserves the readout marginal exactly,
             destroys only its pairing with delta).
PLANT      : r replaced by sign(delta) on a fraction of positions -- must fire.

Also reported, because it is the interpretable form of the same statistic: the readout's partial-sum
difference BEFORE vs AFTER the boundary.  The point sequence [d]G advances by exactly G across a
boundary (representation-independence), so the prediction is null -- but it is MEASURED, not assumed.
"""

import random
import sys

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
A = 0
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
A1 = 0x3086D221A7D46BCDE86C90E49284EB15
B1 = -0xE4437ED6010E88286F547FA90ABFE4C3
A2 = 0x114CA50F7A8E2F3F657C1108D9D44CFD8
B2 = 0x3086D221A7D46BCDE86C90E49284EB15


def rnd_div(a, b):
    q, r = divmod(a, b)
    return q + 1 if 2*r >= b else q


def c1_of(d):
    return rnd_div(d*B2, N)


def c2_of(d):
    return rnd_div(-(d*B1), N)


def glv_norm(d):
    c1, c2 = c1_of(d), c2_of(d)
    k1 = d - c1*A1 - c2*A2
    k2 = -c1*B1 - c2*B2
    return k1*k1 - k1*k2 + k2*k2


def padd(Pt, Q):
    if Pt is None:
        return Q
    if Q is None:
        return Pt
    x1, y1 = Pt
    x2, y2 = Q
    if x1 == x2 and (y1 + y2) % P == 0:
        return None
    if Pt == Q:
        num, den = (3*x1*x1 + A) % P, (2*y1) % P
    else:
        num, den = (y2 - y1) % P, (x2 - x1) % P
    lm = num*pow(den, P - 2, P) % P
    x3 = (lm*lm - x1 - x2) % P
    return (x3, (lm*(x1 - x3) - y1) % P)


def pmul(d, Pt):
    R, Q = None, Pt
    while d:
        if d & 1:
            R = padd(R, Q)
        Q = padd(Q, Q)
        d >>= 1
    return R


def chi2(a):
    a %= P
    return 0 if a == 0 else (1 if pow(a, (P - 1)//2, P) == 1 else -1)


def boundary_scalars(lo, hi, want):
    """exact d where c_2 increments, i.e. -d*B1 + N//2 crosses a multiple of N."""
    out = []
    m = c2_of(lo) + 1
    while len(out) < want:
        # smallest d with -d*B1 + N//2 >= m*N   (B1 < 0 so -B1 > 0)
        num = m*N - N//2
        d = -((-num)//(-B1))
        if d > hi:
            break
        if d >= lo and c2_of(d) != c2_of(d - 1):
            out.append(d)
        m += 1
    return out


def gather(d0, W, G):
    cur = pmul(d0 % N, G)
    r, Nl = [], []
    for i in range(W):
        r.append(chi2(cur[0]))
        Nl.append(glv_norm(d0 + i))
        cur = padd(cur, G)
    return r, Nl


def perm_p(r, delta, R, rng):
    S = sum(r[i]*delta[i] for i in range(len(r)))
    q = r[:]
    ge = 0
    for _ in range(R):
        rng.shuffle(q)
        if abs(sum(q[i]*delta[i] for i in range(len(q)))) >= abs(S):
            ge += 1
    return S, ge + 1, R + 1


if __name__ == "__main__":
    W = int(sys.argv[1]) if len(sys.argv) > 1 else 64
    NI = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    R = 500
    rng = random.Random(20260801)
    G = (Gx, Gy)
    print("=" * 100)
    print("CENTERED SHORT-SCALAR STATISTIC  S_cent = sum r_i * (N_i - mean N)   W=%d, %d intervals/arm"
          % (W, NI))
    print("=" * 100)
    bs = boundary_scalars(2**128, 2**136, NI)
    print("  exact c_2 boundaries located in [2^128, 2^136): %d   (first bitlen %d, last %d)"
          % (len(bs), bs[0].bit_length(), bs[-1].bit_length()))
    print()
    for arm, starts in (("BOUNDARY", [b - W//2 for b in bs]),
                        ("CONTROL ", [rng.randrange(2**128, 2**136) for _ in range(len(bs))])):
        hits = 0
        Ss = []
        jumps = 0
        halfdiff = []
        for d0 in starts:
            r, Nl = gather(d0, W, G)
            mu = sum(Nl)  # keep integers: delta_i = N_i*W - sum(N)
            delta = [v*W - mu for v in Nl]
            if max(delta) - min(delta) > 0 and (max(delta) - min(delta)).bit_length() > 200:
                jumps += 1
            S, a, b = perm_p(r, delta, R, rng)
            Ss.append((a, b))
            if a*20 <= b:
                hits += 1
            halfdiff.append(sum(r[:W//2]) - sum(r[W//2:]))
        print("  %s arm: intervals=%d | contain a lattice-vector-scale jump in delta: %d"
              % (arm, len(starts), jumps))
        print("      exact perm p <= 0.05 in %d/%d (expected %.1f) | min p = %.4f"
              % (hits, len(Ss), 0.05*len(Ss), min(a/b for a, b in Ss)))
        hd = halfdiff
        print("      readout partial-sum difference (before - after): mean %+.2f, sd %.2f,"
              " |mean|/sem = %.2f"
              % (sum(hd)/len(hd), (sum((x - sum(hd)/len(hd))**2 for x in hd)/len(hd))**0.5,
                 abs(sum(hd)/len(hd))/(((sum((x - sum(hd)/len(hd))**2 for x in hd)/len(hd))**0.5
                                        / len(hd)**0.5) + 1e-12)))
    print()
    print("  C-PLANT on the BOUNDARY arm (r := sign(delta) on a fraction of positions):")
    for frac in (100, 50, 25, 10):
        hits = 0
        for d0 in [b - W//2 for b in bs]:
            r, Nl = gather(d0, W, G)
            mu = sum(Nl)
            delta = [v*W - mu for v in Nl]
            rp = r[:]
            k = W*frac//100
            for i in range(k):
                rp[i] = 1 if delta[i] > 0 else -1
            S, a, b = perm_p(rp, delta, R, rng)
            if a*20 <= b:
                hits += 1
        print("      %3d%% planted: fires in %d/%d intervals %s"
              % (frac, hits, len(bs), "OK" if hits > len(bs)//2 else ""))
