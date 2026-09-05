#!/usr/bin/env python3
"""glv_norm_readout_matched_null_v1.py -- the surviving lane, against a MATCHED null.

OBJECT (in scope: the CONVERSION d -> [d]G = (x,y), not the selection of d).
  feature : N(kappa(d)) = k1^2 - k1 k2 + k2^2, the Eisenstein/GLV lattice footprint of the scalar
  readout : a character of the resulting point's x-coordinate
  question: does the scalar's lattice footprint couple to the curve's algebraic geometry?

WHY A NULL IS REQUIRED.  `glv_lattice_feature_prescreen_v1.py`'s T4 row (e.g. Sum_d chi2(x)*N = -192)
was a CONTROL -- built to show the lane is not FORCED to zero, i.e. that the instrument can move.
A nonzero raw sum is not evidence of coupling: any two class functions have a nonzero inner product
at scale ~ sqrt(sum of squares).  The claim "the footprint correlates with the geometry" needs the
statistic compared to a null that preserves every FORCED symmetry and destroys only the putative
coupling.  That is the class-permutation null (cf. curve_native_beam_scan_v2, where a free
permutation manufactured a phantom that the symmetry-preserving null killed on identical data).

THE MATCHED NULL.  Both the readout and N are constant on mu_6 orbits {d, ld, l^2 d, -d, -ld, -l^2 d}
(all of size exactly 6, since 6 | n-1).  So both are CLASS FUNCTIONS on the mu_6 quotient.  The null
permutes the readout's class-values among classes, leaving N and the class structure untouched.

PRE-SCREEN FIRST (mechanical, before any null runs).  A readout chi(x) is legal against a
mu_3-invariant EVEN feature only if chi(beta) = 1 (else the mu_3 orbit-sum annihilates it) and
chi(-1) = 1 (else the parity pairing annihilates it).  This is checked and reported per readout --
several proposed readouts fail it.

CONTROLS.  (C-FORCED) the known-forced pair chi2(y) x N must read exactly 0 in data AND in every
null draw.  (C-PLANT) a synthetic coupling injected into the readout must be detected.

Exact integer arithmetic; exact permutation p-values (integer counts). No floats.
"""

import sys
import random


def legendre(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p - 1)//2, p) == 1 else -1)


def isqrt_int(x):
    lo, hi = 0, x
    while lo < hi:
        mid = (lo + hi + 1)//2
        if mid*mid <= x:
            lo = mid
        else:
            hi = mid - 1
    return lo


def curve_seq(p, A, B):
    """(n, seq) with seq[d] = [d]G as (x,y); requires E(F_p) cyclic."""
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
            num, den = (3*x1*x1 + A) % p, (2*y1) % p
        else:
            num, den = (y2 - y1) % p, (x2 - x1) % p
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
    for G in pts:
        seq, cur = [None], None
        for _ in range(n):
            cur = add(cur, G)
            seq.append(cur)
        if next((i for i in range(1, len(seq)) if seq[i] is None), None) == n:
            return n, seq[:n]
    return None, None


def find_beta(p):
    if p % 3 != 1:
        return None
    for g in range(2, p):
        b = pow(g, (p - 1)//3, p)
        if b != 1 and pow(b, 3, p) == 1:
            return b
    return None


def glv_norm(d, lam, n, span):
    best = None
    for k2 in range(-span, span + 1):
        r = (d - k2*lam) % n
        for k1 in (r, r - n):
            N = k1*k1 - k1*k2 + k2*k2
            if best is None or N < best:
                best = N
    return best


def char_k(x, p, k):
    """chi_k(x) as an integer exponent in Z/k (x^((p-1)/k) is a k-th root of unity);
       returns None if k does not divide p-1."""
    if (p - 1) % k:
        return None
    v = pow(x, (p - 1)//k, p)
    # find e with g0^e = v, g0 a fixed primitive k-th root
    for g in range(2, p):
        g0 = pow(g, (p - 1)//k, p)
        if all(pow(g0, j, p) != 1 for j in range(1, k)):
            break
    e, cur = 0, 1
    for e in range(k):
        if cur == v:
            return e
        cur = cur * g0 % p
    return None


def run(p, A, B, R=2000, seed=12345):
    n, seq = curve_seq(p, A, B)
    if n is None or n % 2 == 0 or n % 3 != 1:
        return None
    beta = find_beta(p)
    G = seq[1]
    lam = next((d for d in range(1, n) if seq[d] == (beta*G[0] % p, G[1])), None)
    if lam is None or (lam*lam + lam + 1) % n:
        return None
    span = 1 + isqrt_int(n)
    N = {d: glv_norm(d, lam, n, span) for d in range(1, n)}

    # ---- mu_6 classes
    seen, classes = set(), []
    for d in range(1, n):
        if d in seen:
            continue
        orb = set()
        for s in (d, (lam*d) % n, (lam*lam*d) % n):
            orb.add(s)
            orb.add((n - s) % n)
        seen |= orb
        classes.append(sorted(orb))
    if any(len(c) != 6 for c in classes):
        return None
    # N constant on classes?
    assert all(len({N[d] for d in c}) == 1 for c in classes), "N not a class function"
    Ncls = [N[c[0]] for c in classes]
    M = len(classes)

    # ---- pre-screen every candidate readout
    print("=" * 100)
    print("p=%-5d n=%-5d  lambda=%-6d beta=%-4d  | mu_6 classes: %d" % (p, n, lam, beta, M))
    legal = []
    for k in (2, 3, 6):
        if (p - 1) % k:
            print("   readout chi_%d(x): k does not divide p-1 -- unavailable" % k)
            continue
        cb = char_k(beta, p, k)
        cm1 = char_k(p - 1, p, k)
        ok = (cb == 0 and cm1 == 0)
        print("   readout chi_%d(x): chi(beta)=zeta_%d^%s  chi(-1)=zeta_%d^%s  -> %s"
              % (k, k, cb, k, cm1, "LEGAL" if ok else
                 "FORCED ZERO against a mu_3-invariant even feature"))
        if ok:
            legal.append(k)
    if not legal:
        print("   no legal readout at this prime")
        return None

    rng = random.Random(seed)
    out = []
    for k in legal:
        # readout as a class function (verify it IS one)
        cls_val = []
        for c in classes:
            vals = {char_k(seq[d][0], p, k) for d in c if seq[d][0] % p != 0}
            if len(vals) != 1:
                cls_val = None
                break
            cls_val.append(next(iter(vals)))
        if cls_val is None:
            print("   chi_%d(x) is NOT constant on mu_6 classes -- skipped" % k)
            continue
        # for k=2 the exponent 0/1 maps to +1/-1
        w = [1 - 2*v for v in cls_val] if k == 2 else [1 if v == 0 else -1 for v in cls_val]
        S = sum(w[i]*Ncls[i] for i in range(M))
        # matched null: permute the readout class-values among classes
        ge = 0
        absS = abs(S)
        for _ in range(R):
            perm = w[:]
            rng.shuffle(perm)
            if abs(sum(perm[i]*Ncls[i] for i in range(M))) >= absS:
                ge += 1
        pval_num, pval_den = ge + 1, R + 1
        print("   chi_%d(x) x N : S = %-8d | matched-null |S'| >= |S| in %d/%d draws"
              "  -> exact perm p = %d/%d" % (k, S, ge, R, pval_num, pval_den))
        out.append((k, S, ge, R))

    # ---- C-FORCED: the known-forced pair must be exactly 0 in data and in every null draw
    cy = {}
    for c in classes:
        for d in c:
            cy[d] = legendre(seq[d][1], p)
    Sf = sum(cy[d]*N[d] for d in range(1, n))
    print("   C-FORCED  Sum_d chi2(y)*N = %d  (must be exactly 0): %s" % (Sf, Sf == 0))

    # ---- C-PLANT: inject a coupling into the readout and confirm detection
    if legal:
        k = legal[0]
        cls_val = []
        for c in classes:
            cls_val.append(char_k(seq[c[0]][0], p, k))
        w = [1 - 2*v for v in cls_val] if k == 2 else [1 if v == 0 else -1 for v in cls_val]
        med = sorted(Ncls)[M//2]
        planted = [1 if Ncls[i] > med else -1 for i in range(M)]
        frac_used = M//5                     # replace 20% of the readout with the planted signal
        wp = w[:]
        for i in range(frac_used):
            wp[i] = planted[i]
        Sp = sum(wp[i]*Ncls[i] for i in range(M))
        ge = 0
        for _ in range(R):
            perm = wp[:]
            rng.shuffle(perm)
            if abs(sum(perm[i]*Ncls[i] for i in range(M))) >= abs(Sp):
                ge += 1
        print("   C-PLANT   20%% planted coupling: S = %-8d  ge = %d/%d -> p = %d/%d  %s"
              % (Sp, ge, R, ge + 1, R + 1,
                 "FIRES" if (ge + 1)*20 <= (R + 1) else "*** PLANT DID NOT FIRE ***"))
    return out


if __name__ == "__main__":
    cands = []
    for p in range(200, 4000):
        if p % 6 != 1:
            continue
        if any(p % q == 0 for q in range(2, isqrt_int(p) + 1)):
            continue
        cands.append(p)
    ran = 0
    for p in cands:
        if ran >= 6:
            break
        for B in (7, 2, 3, 5, 11):
            r = run(p, 0, B, R=2000, seed=1000 + p)
            if r:
                ran += 1
                break
    print("\n" + "=" * 100)
    print("Read the exact permutation p-values above. A p-value near 1 means the raw sum is exactly")
    print("what an uncoupled pair of class functions produces -- i.e. 'S moves' is not a finding.")
