#!/usr/bin/env python3
"""
xdomain_derivation_checks_v1.py — PRE-DATA derivation checks for the four
cross-domain "ports" (RH/LRC methodology -> curve).  Run BEFORE the prereg is
frozen, so that each prediction below is registered as DERIVED (per the Kummer
lesson: a derived prediction is what makes a "positive" implausible enough to
check the instrument first).

Nothing here is a leakage test.  All four checks are algebraic identities whose
outcome is FORCED; a confirmation therefore carries ZERO information as evidence
-- each is an INSTRUMENT CHECK on my own code.  They are run to settle whether
the four proposals' stated premises are true of THIS record's objects.

DC1  (Play 1, mu3 projector).  beta(x,y) = (zeta3*x, y) is the GLV endomorphism,
     acting on E(F_p) as [lambda].  Since beta FIXES y and multiplies the scalar
     by lambda,   V(a) := sum_P chi2(y_P) e(a*d_P/n)   satisfies  V(a) = V(a*lambda).
     => beta maps the twisted cohomology H^1(a) ISOMORPHICALLY to H^1(a*lambda);
     it does not act within fixed-a cohomology, hence cannot split H^1(a).
     Same structural defect as [-1] and zeta4 (NEXT_DIRECTIONS_v1 section 4).

DC2  (Play 4, amicable "boundary condition").  For an amicable pair
     #E(F_p)=n, #Etilde(F_n)=p:  t_p = p+1-n, t_n = n+1-p  =>  t_p + t_n = 2.
     An identity in the DEFINITION of amicability -- zero information.

DC3  (Play 3, phi(n) grid law).  The law selects times with {delta t} = r/n,
     gcd(r,n)=1, giving phi(n) instants per period.  secp's n is PRIME
     => phi(n) = n-1 => EVERY r != 0 qualifies: the selection is vacuous.

DC4  (Play 2, C_T tensor null).  Under the independent-uniform lift model,
     C_T = C_1 (x) C_1 exactly, so its spectrum is {1,1/3,1/9} (x) {1,1/3,1/9}
     and lambda_2 = lambda_3 = 1/3 EXACTLY (algebraic degeneracy, not numeric).
     Any measured |lambda_2 - lambda_3| > 0 is therefore a deviation of the
     arithmetic point set from the model -- which is the quantity to be measured.
"""
import cmath
from sympy.ntheory.residue_ntheory import sqrt_mod, nthroot_mod

# ---------------------------------------------------------------- curve utils
def add_c(A, B, p, b=7):
    if A is None: return B
    if B is None: return A
    x1, y1 = A; x2, y2 = B
    if x1 == x2:
        if (y1 + y2) % p == 0: return None
        lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def points(p, b=7):
    """All affine points of y^2 = x^3 + b over F_p, plus None for O."""
    sq = {}
    for y in range(p):
        sq.setdefault(y * y % p, []).append(y)
    pts = []
    for x in range(p):
        r = (x * x * x + b) % p
        for y in sq.get(r, []):
            pts.append((x, y))
    return pts


def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def dlog_table(p, G, n):
    """d -> point, and point -> d, along the full orbit of a generator G."""
    tab = {}; cur = None
    for d in range(n):
        cur = add_c(cur, G, p) if d else None
        if cur is not None:
            tab[cur] = d
    return tab


# ---------------------------------------------------------------------- DC1
def dc1(pmax=400, b=7):
    """V(a) = V(a*lambda) exactly, for beta the GLV endomorphism."""
    rows = []
    for p in range(11, pmax):
        if not all(p % q for q in range(2, int(p ** .5) + 1)): continue
        if p % 3 != 1: continue                       # need zeta3 in F_p
        pts = points(p, b)
        n = len(pts) + 1
        if n < 5: continue
        # need n prime so the character group is Z/n and orbits are clean
        if not all(n % q for q in range(2, int(n ** .5) + 1)): continue
        # generator
        G = pts[0]
        tab = dlog_table(p, G, n)
        if len(tab) != n - 1: continue
        # zeta3 and lambda
        z3 = nthroot_mod(1, 3, p, all_roots=True)
        z3 = [int(z) for z in z3 if z != 1]
        if not z3: continue
        zeta = z3[0]
        bG = ((zeta * G[0]) % p, G[1])
        if bG not in tab: continue
        lam = tab[bG]                                  # beta = [lam]
        assert (lam ** 3 - 1) % n == 0, (p, lam, n)

        # V(a) for all a
        w = 2j * cmath.pi / n
        V = [0j] * n
        for (x, y) in pts:
            d = tab[(x, y)]; c = legendre(y, p)
            if c == 0: continue
            for a in range(n):
                V[a] += c * cmath.exp(w * (a * d % n))
        worst = max(abs(V[a] - V[a * lam % n]) for a in range(n))
        scale = max(abs(v) for v in V)
        rows.append((p, n, lam, worst, scale))
    return rows


# ---------------------------------------------------------------------- DC2
def dc2():
    p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
    n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
    t_p = p + 1 - n
    t_n = n + 1 - p
    return t_p, t_n, t_p + t_n


# ---------------------------------------------------------------------- DC3
def dc3():
    n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
    from sympy import isprime, totient
    isp = isprime(n)
    return isp, (n - 1 if isp else int(totient(n))), n - 1


# ---------------------------------------------------------------------- DC4
def dc4():
    import numpy as np
    from fractions import Fraction
    # exact per-coordinate chain with stationary law (3/4, 1/8, 1/8) is not
    # needed: the DEGENERACY is a statement about the tensor spectrum alone.
    e = [Fraction(1), Fraction(1, 3), Fraction(1, 9)]
    spec = sorted((a * b for a in e for b in e), reverse=True)
    return spec, spec[1] == spec[2]


if __name__ == "__main__":
    print("=" * 74)
    print("DC1  (Play 1)  V(a) == V(a*lambda) ?   [beta = GLV mu3, fixes y]")
    print("=" * 74)
    r = dc1()
    print(f"{'p':>5} {'n':>5} {'lambda':>7} {'max|V(a)-V(a.lam)|':>21} {'max|V|':>9}")
    for p, n, lam, worst, scale in r:
        print(f"{p:>5} {n:>5} {lam:>7} {worst:>21.3e} {scale:>9.3f}")
    ok = all(w < 1e-8 for *_, w, _ in r)
    print(f"\n  identity holds at every tested prime: {ok}   ({len(r)} primes)")
    print("  => beta maps H^1(a) -> H^1(a*lambda): an ISOMORPHISM between DIFFERENT")
    print("     twisted cohomologies, not an operator on one. It cannot split H^1(a).")

    print()
    print("=" * 74)
    print("DC2  (Play 4)  t_p + t_n  for the secp amicable pair")
    print("=" * 74)
    tp, tn, s = dc2()
    print(f"  t_p = {tp}")
    print(f"  t_n = {tn}")
    print(f"  t_p + t_n = {s}      (identity in the definition; zero information)")

    print()
    print("=" * 74)
    print("DC3  (Play 3)  phi(n) selection at secp")
    print("=" * 74)
    isp, phi, nm1 = dc3()
    print(f"  n prime: {isp};  phi(n) = {phi}")
    print(f"  phi(n) == n-1 : {phi == nm1}  => every r != 0 mod n is coprime to n")
    print("  => the phi(n) law's coprimality SELECTION is vacuous at prime n.")

    print()
    print("=" * 74)
    print("DC4  (Play 2)  tensor-square spectrum degeneracy (exact rationals)")
    print("=" * 74)
    spec, deg = dc4()
    print(f"  spectrum {[str(s) for s in spec]}")
    print(f"  lambda_2 == lambda_3 exactly: {deg}")
    print("  => the model predicts EXACT degeneracy; any split is model deviation.")
