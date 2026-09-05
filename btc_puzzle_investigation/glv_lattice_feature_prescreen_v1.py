#!/usr/bin/env python3
"""glv_lattice_feature_prescreen_v1.py -- PRE-SCREEN the proposed Eisenstein-lattice features.

PROPOSAL UNDER TEST (2026-08-01):
  "every scalar d lifts to an Eisenstein integer kappa = k1 + k2*omega; measure the hexagonal norm
   N = k1^2 - k1*k2 + k2^2 and the sextic sector; also the integer cross-product (determinant) of a
   scalar and its inverse in GLV space."

THE PRE-SCREEN (the rule that has silently mis-specified four probes already).  On a j=0 curve the
readout c(d) = chi_2(y_{[d]G}) satisfies, EXACTLY and by the endomorphism, not statistically:
    c(lambda*d) = c(d)          because [lambda](x,y) = (beta*x, y) leaves y FIXED   -> mu_3-invariant
    c(-d)       = eps * c(d),   eps = chi_2(-1)                                       -> parity eps
secp256k1 has p = 3 mod 4, so eps = -1 and **c is ODD**.

A feature f(d) that is EVEN under d -> -d therefore pairs off exactly:
    Sum_d c(d) f(d) = Sum over {d,-d} of (c(d) - c(d)) f(d) = 0   IDENTICALLY, for every f.
N(kappa) is even (N(-kappa) = N(kappa)).  The det of (kappa(d), kappa(d^-1)) is even (both flip sign).
So both proposed features are FORCED TO ZERO against chi_2(y) -- zero information, no sample size
fixes it.

WHAT THIS SCRIPT DOES.  Verifies the forcing exactly (not statistically), verifies the controls fire,
and verifies the REPAIR: pairing an even feature with an EVEN readout is not forced and does move.

    C1  c(lambda*d) == c(d) for all d                       [the mu_3 forcing, must hold]
    C2  c(-d) == eps*c(d) for all d                         [the parity forcing, must hold]
    C3  N(kappa(-d)) == N(kappa(d)) for all d               [the feature is even, must hold]
    T1  Sum_d c(d)*f(N(kappa(d))) == 0 EXACTLY, several f   [the norm probe is FORCED]
    T2  Sum_d c(d)*det(kappa(d),kappa(d^-1)) == 0 EXACTLY   [the det probe is FORCED]
    T3  Sum_d c(d)*g(sector(d)) for all 6 sector characters [only the ODD ones can survive]
    T4  REPAIR: even readout chi_2(x) vs the same features  [control: must be NONZERO]

Integer arithmetic only; passes check_no_float.py.
"""

import sys


def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1)//2, p) == 1 else -1


def curve_points_cyclic(p, A, B):
    """return (n, [P_0..P_{n-1}]) for a cyclic E(F_p), P_d = [d]G, as (x,y) or None for O."""
    def add(P, Q):
        if P is None:
            return Q
        if Q is None:
            return P
        x1, y1 = P
        x2, y2 = Q
        if x1 == x2 and (y1 + y2) % p == 0:
            return None
        if P == Q:
            num = (3*x1*x1 + A) % p
            den = (2*y1) % p
        else:
            num = (y2 - y1) % p
            den = (x2 - x1) % p
        lam = num * pow(den, p - 2, p) % p
        x3 = (lam*lam - x1 - x2) % p
        y3 = (lam*(x1 - x3) - y1) % p
        return (x3, y3)

    pts = []
    for x in range(p):
        r = (x*x % p * x + A*x + B) % p
        for y in range(p):
            if y*y % p == r:
                pts.append((x, y))
    n = len(pts) + 1
    # find a generator
    for G in pts:
        seq = [None]
        cur = None
        for _ in range(n):
            cur = add(cur, G)
            seq.append(cur)
        # order = first index >0 where cur is None
        order = next((i for i in range(1, len(seq)) if seq[i] is None), None)
        if order == n:
            return n, seq[:n], add
    return None, None, add


def find_beta(p):
    """an element of F_p of exact order 3 (exists iff p = 1 mod 3)."""
    if p % 3 != 1:
        return None
    for g in range(2, p):
        b = pow(g, (p - 1)//3, p)
        if b != 1 and pow(b, 3, p) == 1:
            return b
    return None


def glv_kappa(d, lam, n, span):
    """minimal-norm (k1,k2) with k1 + k2*lam = d (mod n), N = k1^2 - k1 k2 + k2^2.
       Exhaustive over |k2| <= span with k1 the near-zero representative -- exact, no floats."""
    best = None
    for k2 in range(-span, span + 1):
        r = (d - k2*lam) % n
        for k1 in (r, r - n):
            N = k1*k1 - k1*k2 + k2*k2
            if best is None or N < best[0] or (N == best[0] and (k1, k2) < best[1:]):
                best = (N, k1, k2)
    return best[1], best[2], best[0]


def sector(k1, k2):
    """which of the 6 sextants of the Eisenstein lattice kappa lies in (0..5), by sign pattern.
       Uses the three linear forms k2, k1, k1-k2 -- exact integer comparisons."""
    a, b, c = k1, k2, k1 - k2
    # a canonical 6-fold sector index from the sign pattern of (a, b, c)
    key = (1 if a > 0 else (0 if a == 0 else -1),
           1 if b > 0 else (0 if b == 0 else -1),
           1 if c > 0 else (0 if c == 0 else -1))
    table = {(1, 1, 1): 0, (1, 1, -1): 1, (-1, 1, -1): 2,
             (-1, -1, -1): 3, (-1, -1, 1): 4, (1, -1, 1): 5}
    return table.get(key, -1)


def run(p, A, B):
    n, seq, add = curve_points_cyclic(p, A, B)
    if n is None or n % 2 == 0 or n % 3 != 1:
        return None
    beta = find_beta(p)
    if beta is None:
        return None
    eps = legendre(p - 1, p)
    G = seq[1]
    # lambda: [lambda]G = (beta*x_G, y_G)
    target = (beta*G[0] % p, G[1])
    lam = next((d for d in range(1, n) if seq[d] == target), None)
    if lam is None:
        return None
    assert (lam*lam + lam + 1) % n == 0, "lambda is not a primitive cube root mod n"

    span = 1 + isqrt_int(n)
    kap = {}
    for d in range(1, n):
        kap[d] = glv_kappa(d, lam, n, span)

    c = {d: legendre(seq[d][1], p) for d in range(1, n)}          # chi_2(y)  -- ODD when eps = -1
    cx = {d: legendre(seq[d][0], p) for d in range(1, n)}         # chi_2(x)  -- EVEN

    # ---- controls
    C1 = all(c[(lam*d) % n] == c[d] for d in range(1, n))
    C2 = all(c[(n - d) % n] == eps*c[d] for d in range(1, n))
    C3 = all(kap[(n - d) % n][2] == kap[d][2] for d in range(1, n))
    C4 = all(cx[(n - d) % n] == cx[d] for d in range(1, n))

    # ---- T1: norm features against the ODD readout
    feats = {
        "N": lambda d: kap[d][2],
        "N mod 3": lambda d: kap[d][2] % 3,
        "N mod 7": lambda d: kap[d][2] % 7,
        "[N even]": lambda d: 1 if kap[d][2] % 2 == 0 else 0,
    }
    T1 = {name: sum(c[d]*f(d) for d in range(1, n)) for name, f in feats.items()}

    # ---- T2: det(kappa(d), kappa(d^-1)) against the ODD readout
    def det_feat(d):
        di = pow(d, n - 2, n)
        if di == 0:
            return 0
        a1, a2, _ = kap[d]
        b1, b2, _ = kap[di]
        return a1*b2 - a2*b1
    T2 = sum(c[d]*det_feat(d) for d in range(1, n))
    T2c = sum(cx[d]*det_feat(d) for d in range(1, n))

    # ---- T3: the 6 sector "characters" as integer weightings, odd vs even
    #      w_k(s) = 1 if (s*k) % 6 in the first half else -1 -- crude but parity-faithful:
    #      we test the exact parity-relevant one, (-1)^s, and the even indicator set.
    T3_odd = sum(c[d]*((-1)**sector(kap[d][0], kap[d][1])) for d in range(1, n))
    T3_even = sum(c[d]*(1 if sector(kap[d][0], kap[d][1]) in (0, 1, 2) else 0)
                  for d in range(1, n))

    # ---- T4: REPAIR -- the same even features against the EVEN readout chi_2(x)
    T4 = {name: sum(cx[d]*f(d) for d in range(1, n)) for name, f in feats.items()}

    print("=" * 96)
    print("p=%-5d (p mod 4=%d, eps=%+d)  n=%-5d  lambda=%-6d beta=%-5d   [j=0, mu_3 present]"
          % (p, p % 4, eps, n, lam, beta))
    print("  CONTROLS   C1 c(lam*d)==c(d): %-5s | C2 c(-d)==eps*c(d): %-5s |"
          " C3 N(kap(-d))==N(kap(d)): %-5s | C4 chi2(x) even: %-5s"
          % (C1, C2, C3, C4))
    print("  T1  ODD readout chi_2(y) vs EVEN norm features -- all must be EXACTLY 0:")
    for name, v in T1.items():
        print("        Sum_d c(d)*%-10s = %-6d   %s" % (name, v, "FORCED ZERO" if v == 0 else "*** NONZERO ***"))
    print("  T2  ODD readout vs det(kappa(d), kappa(d^-1)) : %-8d  %s"
          % (T2, "FORCED ZERO" if T2 == 0 else "*** NONZERO ***"))
    print("  T3  sector, odd weighting (-1)^s : %-6d | sector, even indicator : %-6d"
          % (T3_odd, T3_even))
    print("  T4  REPAIR -- EVEN readout chi_2(x) vs the same features (control: should MOVE):")
    for name, v in T4.items():
        print("        Sum_d cx(d)*%-10s = %-6d  %s" % (name, v, "moves" if v != 0 else "zero"))
    print("        Sum_d cx(d)*det        = %-6d  %s" % (T2c, "moves" if T2c != 0 else "zero"))
    return (C1, C2, C3, all(v == 0 for v in T1.values()), T2 == 0,
            any(v != 0 for v in T4.values()) or T2c != 0)


def isqrt_int(x):
    lo, hi = 0, x
    while lo < hi:
        mid = (lo + hi + 1)//2
        if mid*mid <= x:
            lo = mid
        else:
            hi = mid - 1
    return lo


if __name__ == "__main__":
    rows = []
    for (p, A, B) in [(43, 0, 7), (67, 0, 7), (79, 0, 7), (127, 0, 7), (163, 0, 7)]:
        r = run(p, A, B)
        if r:
            rows.append(r)
    print("\n" + "=" * 96)
    ok = all(all(r[:5]) for r in rows)
    print("VERDICT over %d j=0 curves:" % len(rows))
    print("  controls C1-C3 hold everywhere            : %s" % all(all(r[:3]) for r in rows))
    print("  ALL norm features forced to EXACTLY zero  : %s" % all(r[3] for r in rows))
    print("  det(d, d^-1) feature forced to zero       : %s" % all(r[4] for r in rows))
    print("  REPAIR (even readout) actually moves      : %s" % all(r[5] for r in rows))
    sys.exit(0 if ok else 1)
