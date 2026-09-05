#!/usr/bin/env sage
# algebraic_branch_confirmation_v1.sage
# ============================================================================
# Thread #4 (2026-08-01): branch confirmation of the algebraic-layer law.
#
# The record (RESULT_algebraic_number_layer_v1.md §2) verified the law
#   minpoly deg = 4(n-1)/3,  multiplicity 3
# only in the chi2(-1) = -1 branch (p=43, 67, 127). This script confirms (or refines)
# the law in the chi2(-1) = +1 branch (p == 1 mod 4), at primes large enough to avoid
# the n=7 / p=13 small-n degeneracy (where the char-poly coefficients collapse to Q).
#
# FINDING: the law is BRANCH-DEPENDENT.
#   chi2(-1) = -1 : minpoly deg = 4(n-1)/3,  mult 3   (record; p = 43, 67, 127)
#   chi2(-1) = +1 : minpoly deg = 4(n-1)/6,  mult 6   (new;  p = 61, 97)
# The +1 branch has twice the multiplicity and half the minpoly degree -- a finer
# orbit structure, consistent with an extra factor-of-2 symmetry when -1 is a square
# mod p (so chi2(-1)=+1).
#
# EXACT ARITHMETIC (CLAUDE.md no-float rule). All cyclotomic-field / Q arithmetic;
# no float in the signal path.
# ============================================================================
import sys
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core
from collections import Counter


def build_L(p, a, K, z, n):
    """L_a(T) in K[T] (reused from anew_eigenvalue_identify_v3.sage)."""
    dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
    V1 = sum(h1[d] * z ** ((a * d) % n) for d in range(n))
    V2 = sum(h2[d] * z ** ((a * d) % n) for d in range(n))
    leg = 1 if p % 4 == 1 else -1
    e1 = -V1; e2 = (V1 ** 2 + V2) / 2; e3 = leg * p * e1; e4 = K(p ** 2)
    R = PolynomialRing(K, 'T'); T = R.gen()
    return T ** 4 - e1 * T ** 3 + e2 * T ** 2 - e3 * T + e4


def apply_hom_to_poly(phi, P, Rring):
    T = Rring.gen()
    return sum(phi(c) * T ** i for i, c in enumerate(P.list()))


def Q_norm(L, Kn, zn, n):
    """N_{Q(zeta_n)/Q}(L) in QQ[T]."""
    RKn = PolynomialRing(Kn, 'T'); P = RKn(1)
    for c in (c for c in range(1, n) if gcd(c, n) == 1):
        P *= apply_hom_to_poly(Kn.hom([zn ** c]), L, RKn)
    return P.change_ring(QQ)


def branch_law(p, a=1):
    """Compute the Q-factorization of the norm and report the branch-dependent law.
    Returns dict(p, n, branch, degP, minpoly_deg, multiplicity, law_holds)."""
    n = core.curve_order(p)
    assert core.is_prime(n), (p, n)
    leg = 1 if p % 4 == 1 else -1
    branch = "+1" if leg == 1 else "-1"
    Kn = CyclotomicField(n); zn = Kn.gen()
    L = build_L(p, a, Kn, zn, n)
    PQ = Q_norm(L, Kn, zn, n)
    facQ = PQ.factor()
    degmult = Counter()
    for f, e in facQ:
        degmult[f.degree()] += e
    items = sorted(degmult.items())
    d, m = items[0]
    if leg == -1:
        law_holds = (d == 4 * (n - 1) // 3 and m == 3 and len(items) == 1)
    else:
        law_holds = (d == 4 * (n - 1) // 6 and m == 6 and len(items) == 1)
    return dict(p=p, n=n, branch=branch, degP=PQ.degree(),
                factorization=dict(items), minpoly_deg=d, multiplicity=m,
                law_holds=law_holds)


def report(r):
    print("p=%-4d n=%-4d branch=chi2(-1)=%s | degP=%d | Q-factor {deg:mult}: %s"
          % (r['p'], r['n'], r['branch'], r['degP'], r['factorization']), flush=True)
    print("    minpoly deg=%d  mult=%d  | law_holds=%s"
          % (r['minpoly_deg'], r['multiplicity'], r['law_holds']), flush=True)


if __name__ == "__main__":
    print("=== chi2(-1) = -1 branch (record: 43, 67, 127) ===", flush=True)
    for p in (43, 67, 127):
        report(branch_law(p))
    print(flush=True)
    print("=== chi2(-1) = +1 branch (NEW: 61, 97) ===", flush=True)
    for p in (61, 97):
        report(branch_law(p))
