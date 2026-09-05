#!/usr/bin/env python3
"""
n1_vsign_decide_v1.py -- independent recomputation of the `v > 0` COUNT.

Implements the audit's B1/B2/B5 edits directly:
  * mu6-COSET PRODUCT  Q_p(Y) = prod_{cosets}(Y - e2(rep))  -- always degree (n-1)/6,
    so `deg m_p = (n-1)/6` is never asserted (B5(ii)); counts are with multiplicity.
  * INTEGER TAYLOR SHIFT + DESCARTES sign count, not Sturm (B1).  Exact, not an upper bound,
    because Q_p is totally real -- and the run SELF-CERTIFIES that with V(g) + V(g(-Z)) = deg g.
  * STRICT boundary (B5(i)): the test is a root STRICTLY below -2p.  Q_p(-2p) = 0 is an exact
    integer evaluation meaning v = 0, which SATISFIES v <= 0 and is reported as confirming,
    never as ABSTAIN.

SIN (p=3 mod 4): v = -(e2+2p)/(4p), so v > 0  <=>  e2 < -2p.
COS (p=1 mod 4): v =  (e2-2p)/(4p), so v > 0  <=>  e2 > +2p.

Exact integer arithmetic throughout.  The only float is the optional display of max v, which is
computed from exact isolating intervals and decides nothing.
"""
import sys, time
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from audit_n1_vsign_v2_core import (is_prime, curve_order, dlog_table, hist_k1, hist_k2,
                                    reduce_phi_prime, sigma)
from n1_forced_identity_v1 import mulF, red

B = 7


def mu6_subgroup(n):
    """the order-6 subgroup of (Z/n)^*  (6 | n-1 is forced)."""
    assert (n - 1) % 6 == 0
    for g in range(2, n):
        if all(pow(g, (n - 1) // q, n) != 1 for q in _prime_factors(n - 1)):
            break
    h = pow(g, (n - 1) // 6, n)
    return sorted({pow(h, i, n) for i in range(6)})


def _prime_factors(m):
    r, d = set(), 2
    while d * d <= m:
        while m % d == 0:
            r.add(d); m //= d
        d += 1
    if m > 1:
        r.add(m)
    return r


def coset_reps(n):
    mu = mu6_subgroup(n)
    assert len(mu) == 6, f"mu6 has order {len(mu)}"
    seen, reps = set(), []
    for a in range(1, n):
        if a in seen:
            continue
        orb = {a * m % n for m in mu}
        assert len(orb) == 6, f"orbit of {a} has size {len(orb)}"
        seen |= orb
        reps.append(a)
    assert len(reps) == (n - 1) // 6
    return reps, mu


def sigma_vec(A, c, n):
    """Galois zeta -> zeta^c on a length-(n-1) vector in the Phi_n basis."""
    full = list(A) + [0]
    return reduce_phi_prime(sigma(full, c, n), n)


def coset_product(e2, reps, n):
    """Q(Y) = prod_reps (Y - sigma_rep(e2)), coefficients carried in Z[zeta_n]; must come out rational."""
    zero = [0] * (n - 1)
    one = [1] + [0] * (n - 2)
    Q = [one[:]]                                  # Q[i] = coefficient of Y^i
    for c in reps:
        v = sigma_vec(e2, c, n)
        new = [zero[:] for _ in range(len(Q) + 1)]
        for i, qi in enumerate(Q):
            new[i + 1] = [a + b for a, b in zip(new[i + 1], qi)]           # Y * Q
            t = mulF(qi, v, n)
            new[i] = [a - b for a, b in zip(new[i], t)]                    # - v * Q
        Q = new
    out = []
    for i, qi in enumerate(Q):
        assert all(x == 0 for x in qi[1:]), f"coefficient {i} of Q is not rational"
        out.append(qi[0])
    return out                                     # integer coefficients, low -> high


def taylor_shift(coeffs, s):
    """g(Z) = f(Z + s), exact integer Horner-style synthetic division.  coeffs low->high."""
    c = list(coeffs)
    d = len(c) - 1
    for k in range(d):
        for i in range(d - 1, k - 1, -1):
            c[i] += s * c[i + 1]
    return c


def sign_variations(coeffs):
    ch, prev = 0, 0
    for x in coeffs:
        s = (x > 0) - (x < 0)
        if s == 0:
            continue
        if prev and s != prev:
            ch += 1
        prev = s
    return ch


def decide(p, verbose=True):
    n = curve_order(p, B)
    assert is_prime(n)
    sin = (p % 4 == 3)
    dl = dlog_table(p, n, B)
    h1, h2 = hist_k1(p, n, dl, B), hist_k2(p, n, dl, B)
    V1, V2 = red(h1, n), red(h2, n)
    W = [a + b for a, b in zip(mulF(V1, V1, n), V2)]
    assert all(x % 2 == 0 for x in W), "e2 not an algebraic integer"
    e2 = [x // 2 for x in W]

    reps, _ = coset_reps(n)
    Q = coset_product(e2, reps, n)
    d = len(Q) - 1
    assert d == (n - 1) // 6

    thr = -2 * p if sin else 2 * p
    boundary = sum(Q[i] * thr ** i for i in range(len(Q)))     # exact integer Q(thr)

    g = taylor_shift(Q, thr)                                   # g(Z) = Q(Z + thr)
    galt = [g[i] * (1 if i % 2 == 0 else -1) for i in range(len(g))]
    n_neg, n_pos = sign_variations(galt), sign_variations(g)
    real_cert = (n_neg + n_pos == d)                           # free total-reality certificate

    # SIN: v>0  <=> e2 < -2p  => roots of Q strictly BELOW thr  => negative roots of g
    # COS: v>0  <=> e2 > +2p  => roots of Q strictly ABOVE thr  => positive roots of g
    count = n_neg if sin else n_pos

    if verbose:
        print(f"p={p:>6}  n={n:<6} d=(n-1)/6={d:<5} {'SIN' if sin else 'COS'}  "
              f"threshold e2 {'<' if sin else '>'} {thr}")
        print(f"          Q monic deg {d}, leading {Q[-1]}, Q({thr}) = "
              f"{'0  *** BOUNDARY: v = 0 exactly, CONFIRMS v<=0 ***' if boundary == 0 else '!= 0'}")
        print(f"          Descartes: V(g)={n_pos}  V(g(-Z))={n_neg}  sum={n_neg+n_pos} vs deg {d}  "
              f"total-reality self-certificate: {'PASS' if real_cert else 'FAIL'}")
        print(f"          ==> # mu6 classes with v > 0 : {count}  of {d}")
    return dict(p=p, n=n, d=d, sin=sin, count=count, boundary=boundary,
                real_cert=real_cert, Q=Q, thr=thr)


if __name__ == "__main__":
    for p in [int(t) for t in sys.argv[1:]]:
        t0 = time.time()
        r = decide(p)
        print(f"          ({time.time()-t0:.1f}s)\n", flush=True)
