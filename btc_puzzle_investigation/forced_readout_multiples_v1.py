#!/usr/bin/env python3
"""
forced_readout_multiples_v1.py — ARM C: the IDEA behind proposal 3, not its method.

The proposal's method (the phi(n) coprimality selection) is vacuous at prime n
(DC3).  Its IDEA is not:

    "Are there specific multiples [k]P where the point is structurally forced,
     so that the chi2(y) signature becomes entirely predictable for that k,
     yielding a deterministic oracle for internal scalar bits?"

That is a well-posed, exhaustively decidable question, and it has never been asked
of this record.  Ask it directly.

DEFINITION (the object).  Call k in (Z/n)^* a FORCED multiple if there is a
constant c in {+1,-1} with

        chi2( y_{[k]P} )  =  c * chi2( y_P )      for EVERY affine P with y != 0.

Equivalently the 2x2 contingency table of (chi2 y_P, chi2 y_{[k]P}) has exactly two
non-zero cells, arranged as a bijection.  No approximation, no threshold, no
statistic -- an exact integer table over the complete point set.

PRE-COMMITTED READING (registered before the sweep):
  * If the forced set is exactly mu_6 = {+-1, +-lambda, +-lambda^2}: the forcing is
    the ACTION OF Aut(E) and therefore carries ZERO information about d -- knowing
    chi2(y_{[lambda]P}) = chi2(y_P) tells you nothing you did not already know from P.
    Report it as a complete characterisation, NOT as an oracle.
  * If ANY k outside mu_6 is forced: that is an unforced positive and the arm's
    interesting outcome -- a deterministic relation between a scalar multiple and
    the readout that is not an automorphism.  Report the k, its order, and whether
    it is d-informative.
  * If the forced set is SMALLER than mu_6: my derivation is wrong; the instrument
    is suspect and must be checked before anything else.

Derivations fixing the mu_6 expectation (so a "positive" is implausible enough that
the instrument gets checked first -- the Kummer lesson):
  beta(x,y) = (zeta3 x, y) FIXES y  => chi2(y_{[lambda]P}) = chi2(y_P), c = +1.
  [-1](x,y) = (x,-y)               => chi2(y_{-P})       = chi2(-1) chi2(y_P).
So all six elements of mu_6 = Aut(E) for j = 0 are forced a priori; the ONLY open
part of this sweep is whether anything ELSE is.

No leakage, key-recovery or ECDLP claim.  Exact integers throughout.
"""
from sympy.ntheory.residue_ntheory import sqrt_mod, nthroot_mod

B = 7


def add_c(A, C, p):
    if A is None: return C
    if C is None: return A
    x1, y1 = A; x2, y2 = C
    if x1 == x2:
        if (y1 + y2) % p == 0: return None
        lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def setup(p):
    """Prime-order y^2=x^3+7 over F_p; returns orbit list, n, lambda, chi2 array."""
    G = None
    for x in range(1, p):
        r = (x * x * x + B) % p
        if r and pow(r, (p - 1) // 2, p) == 1:
            y = sqrt_mod(r, p)
            if y: G = (x, int(y)); break
    if G is None: return None
    pts = [None]; cur = None
    for _ in range(4 * p):
        cur = add_c(cur, G, p); pts.append(cur)
        if cur is None: break
    n = len(pts) - 1
    if pts[n] is not None or not all(n % q for q in range(2, int(n ** .5) + 1)):
        return None
    pts = pts[:n]                                  # pts[d] = [d]G, pts[0] = O
    idx = {pts[d]: d for d in range(1, n)}
    # lambda from the GLV endomorphism
    z3 = [int(z) for z in nthroot_mod(1, 3, p, all_roots=True) if z != 1]
    if not z3: return None
    bG = ((z3[0] * pts[1][0]) % p, pts[1][1])
    if bG not in idx: return None
    lam = idx[bG]
    chi = [0] * n
    for d in range(1, n):
        chi[d] = legendre(pts[d][1], p)
    return pts, n, lam, chi


def forced_set(n, chi):
    """Exact: all k with chi[k*d mod n] = c*chi[d] for every d with chi[d] != 0."""
    out = []
    live = [d for d in range(1, n) if chi[d] != 0]
    for k in range(1, n):
        c = None; ok = True
        for d in live:
            a, b = chi[d], chi[k * d % n]
            if b == 0: ok = False; break
            r = a * b                              # +1 => same sign, -1 => flipped
            if c is None: c = r
            elif c != r: ok = False; break
        if ok and c is not None:
            out.append((k, c))
    return out


def main():
    print("=" * 78)
    print("ARM C — which scalar multiples FORCE the chi2(y) readout?   (exhaustive)")
    print("=" * 78)
    print(f"{'p':>6} {'n':>6} {'lambda':>7} {'|forced|':>9}  forced set (k, sign)")
    anomalies = []
    for p in range(11, 700):
        if not all(p % q for q in range(2, int(p ** .5) + 1)): continue
        if p % 3 != 1: continue
        s = setup(p)
        if s is None: continue
        pts, n, lam, chi = s
        F = forced_set(n, chi)
        mu6 = {1, lam % n, lam * lam % n,
               n - 1, (n - lam) % n, (n - lam * lam % n) % n}
        got = {k for k, _ in F}
        extra = sorted(got - mu6); missing = sorted(mu6 - got)
        tag = ""
        if extra: tag += f"  <-- EXTRA {extra}"; anomalies.append((p, extra))
        if missing: tag += f"  <-- MISSING {missing}"; anomalies.append((p, missing))
        print(f"{p:>6} {n:>6} {lam:>7} {len(F):>9}  "
              f"{sorted(F)}{tag}")
    print()
    print(f"  mu_6 = {{+-1, +-lambda, +-lambda^2}} has 6 elements (Aut(E) for j=0).")
    print(f"  primes where the forced set is EXACTLY mu_6, no more, no less: "
          f"{'ALL' if not anomalies else 'NOT ALL'}")
    if anomalies:
        print(f"  ANOMALIES (the arm's interesting outcome): {anomalies}")
    else:
        print("  => The forced multiples are exactly the AUTOMORPHISM GROUP.")
        print("     An automorphism-forced relation is information-free about d:")
        print("     chi2(y_[lambda]P) = chi2(y_P) is a statement about the SAME point's")
        print("     y-coordinate, not about the scalar. No oracle follows.")
        print("     This is a COMPLETE characterisation (every k tested, exact table),")
        print("     not a null at a noise floor.")


if __name__ == "__main__":
    main()
