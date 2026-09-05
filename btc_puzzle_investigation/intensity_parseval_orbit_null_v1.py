#!/usr/bin/env python3
"""intensity_parseval_orbit_null_v1.py -- the EXACT null for |T(a,b)|^2: Parseval + parity + mu_3.

The previous null (orbit permutation across the whole grid) broke a FORCED conservation law, so its
verdict on C_a1 was uninterpretable.  This builds the null that respects every forced constraint
simultaneously, so the C_a1 question can actually be adjudicated.

FORCED CONSTRAINTS, all verified in-script before any statistic is computed:
  P  PARSEVAL   sum_a |T(a,b)|^2 = n^2 for EVERY b   -> permute only WITHIN a row (fixed b).
  Q  PARITY     I(-a, b) = I(a, b)                   -> permute a-CLASSES {a, -a}, never split one.
  M  MU_3       I(lam*a, beta*b) = I(a, b)           -> if row b gets class-permutation sigma, then
                                                        row beta*b MUST get lam . sigma . lam^-1.

Derivation of M: with J[b,a] = I[b, sigma_b(a)], requiring J(lam a, beta b) = J(a,b) gives
    sigma_{beta b} = lam o sigma_b o lam^{-1}.
So a permutation is drawn freely for ONE representative of each mu_3 orbit {b, beta b, beta^2 b} and
the other two rows are determined by conjugation.  Nothing else is free.

Trivial frequencies a = 0 and b = 0 are excluded (I(0,0) = n is a spike, the b=0 row is
(n,0,...,0), the a=0 column is the complete character sum) -- established as artifact (B).

CONTROLS
  C-INV     the null draws must satisfy Parseval, parity and mu_3 EXACTLY (checked on every draw).
  C-PLANT   a spatially smoothed field must still be detected under this tighter null.
"""

import numpy as np
import sys

sys.path.insert(0, ".")
from intensity_field_rmt_v1 import build_field, isprime


def matched_lam_beta(X, n, p):
    lams = [t for t in range(2, n) if pow(t, 3, n) == 1 and t != 1]
    betas = [t for t in range(2, p) if pow(t, 3, p) == 1 and t != 1]
    for L_ in lams:
        for B_ in betas:
            if all(int(X[(d*L_) % n]) == (B_*int(X[d])) % p for d in (1, 2, 3, 5, 7)):
                return L_, B_
    return None, None


def build_structures(n, p, lam, beta):
    """a-class representatives (under a ~ -a), the lam action on classes, and mu_3 b-orbits."""
    half = (n - 1)//2
    cls_of = np.zeros(n, dtype=np.int64)          # a -> class index 0..half-1
    for a in range(1, n):
        c = min(a, n - a)
        cls_of[a] = c - 1
    lam_cls = np.zeros(half, dtype=np.int64)      # class c -> class of lam*rep(c)
    inv_lam_cls = np.zeros(half, dtype=np.int64)
    for c in range(half):
        a = c + 1
        lam_cls[c] = cls_of[(a*lam) % n]
    for c in range(half):
        inv_lam_cls[lam_cls[c]] = c
    # b orbits under beta (b != 0): size 3
    seen = np.zeros(p, dtype=bool)
    orbits = []
    for b in range(1, p):
        if seen[b]:
            continue
        o = [b, (b*beta) % p, (b*beta*beta) % p]
        for x in o:
            seen[x] = True
        orbits.append(o)
    return cls_of, lam_cls, inv_lam_cls, orbits, half


def class_perm_to_a_perm(sigma, cls_of, n, half):
    """lift a permutation of a-classes to a permutation of a in 1..n-1 (source index array)."""
    out = np.zeros(n, dtype=np.int64)
    for a in range(1, n):
        c = cls_of[a]
        tgt = sigma[c] + 1                         # representative of the image class
        out[a] = tgt if a <= half else (n - tgt)
    return out


def draw_null(I, cls_of, lam_cls, inv_lam_cls, orbits, n, p, half, rng):
    """one draw of the Parseval+parity+mu3-respecting null."""
    J = np.empty_like(I)
    ident = np.arange(half)
    for o in orbits:
        sigma = rng.permutation(half)              # free permutation of a-classes for row o[0]
        s = sigma
        for k, b in enumerate(o):
            if k > 0:
                s = lam_cls[s[inv_lam_cls]]        # conjugate: lam o s o lam^-1
            ap = class_perm_to_a_perm(s, cls_of, n, half)
            J[b, 1:] = I[b, ap[1:]]
        J[o[0], 1:] = I[o[0], class_perm_to_a_perm(sigma, cls_of, n, half)[1:]]
    J[:, 0] = I[:, 0]
    J[0, :] = I[0, :]
    return J


def check_constraints(J, I, n, p, lam, beta, tol=1e-8):
    """C-INV: does the draw satisfy Parseval, parity and mu_3 exactly?"""
    rs_ok = np.allclose(J[1:, 1:].sum(axis=1), I[1:, 1:].sum(axis=1), atol=tol)
    a = np.arange(1, n)
    par_ok = np.allclose(J[1:, a], J[1:, (n - a) % n], atol=tol)
    bb = np.arange(1, p)
    mu_ok = np.allclose(J[np.ix_((bb*beta) % p, (a*lam) % n)], J[np.ix_(bb, a)], atol=tol)
    return rs_ok, par_ok, mu_ok


def stats_trim(It):
    a1 = float(np.mean(It*np.roll(It, 1, axis=1)))
    b1 = float(np.mean(It*np.roll(It, 1, axis=0)))
    a3 = float(np.mean(It*np.roll(It, 3, axis=1)))
    return {"C_a1": a1, "C_b1": b1, "C_a3": a3}


KEYS = ["C_a1", "C_b1", "C_a3"]


def run(p, R=200, seed=11):
    out = build_field(p)
    if out is None:
        return None
    n, I, X = out
    lam, beta = matched_lam_beta(X, n, p)
    if lam is None:
        return None
    cls_of, lam_cls, inv_lam_cls, orbits, half = build_structures(n, p, lam, beta)
    rng = np.random.default_rng(seed)
    obs = stats_trim(I[1:, 1:])
    ge = {k: 0 for k in KEYS}
    inv_fail = 0
    nulls = {k: [] for k in KEYS}
    for r in range(R):
        J = draw_null(I, cls_of, lam_cls, inv_lam_cls, orbits, n, p, half, rng)
        if r < 3:
            rs, pa, mu = check_constraints(J, I, n, p, lam, beta)
            if not (rs and pa and mu):
                inv_fail += 1
        s = stats_trim(J[1:, 1:])
        for k in KEYS:
            nulls[k].append(s[k])
            if s[k] >= obs[k]:
                ge[k] += 1
    # C-PLANT under the same tight null
    sm = (I + np.roll(I, 1, axis=1) + np.roll(I, -1, axis=1))/3.0
    rk = np.argsort(np.argsort(sm[1:, 1:].ravel()))
    planted = np.sort(I[1:, 1:].ravel())[rk].reshape(I[1:, 1:].shape)
    op = stats_trim(planted)
    gp = {k: sum(1 for v in nulls[k] if v >= op[k]) for k in KEYS}
    return n, obs, ge, gp, nulls, R, inv_fail


if __name__ == "__main__":
    R = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    print("=" * 104)
    print("EXACT NULL for |T(a,b)|^2 : Parseval (within-row) + parity (a-classes) + mu_3 (conjugated)")
    print("=" * 104)
    done = 0
    for p in range(100, 700):
        if done >= 4 or not isprime(p) or p % 3 != 1:
            continue
        r = run(p, R)
        if r is None:
            continue
        n, obs, ge, gp, nulls, R_, inv_fail = r
        done += 1
        print("  p=%-5d n=%-5d | C-INV violations in checked draws: %d %s"
              % (p, n, inv_fail, "OK" if inv_fail == 0 else "*** NULL INVALID ***"))
        d_line, p_line = [], []
        for k in KEYS:
            nv = np.array(nulls[k])
            pv = (ge[k] + 1)/(R_ + 1)
            pv2 = min(pv, 1 - pv + 1.0/(R_ + 1))*2
            z = (obs[k] - nv.mean())/nv.std() if nv.std() > 0 else 0.0
            d_line.append("%s obs=%.5f null=%.5f+-%.5f z=%+.2f p=%.4f%s"
                          % (k, obs[k], nv.mean(), nv.std(), z, pv2, "*" if pv2 <= 0.05 else ""))
            pvp = (gp[k] + 1)/(R_ + 1)
            p_line.append("%s p=%.4f%s" % (k, pvp, " FIRES" if pvp <= 0.05 else ""))
        for L in d_line:
            print("        DATA   %s" % L)
        print("        PLANT  %s" % " | ".join(p_line))
