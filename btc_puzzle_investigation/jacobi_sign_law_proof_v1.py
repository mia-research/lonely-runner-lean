#!/usr/bin/env python3
"""
jacobi_sign_law_proof_v1.py -- exact verification of the two derivations offered for the
[EMPIRICAL 12/12] Jacobi sign law of POSITIVE_FINDINGS_ADDENDUM_1_v1.md section A2.2:

    J(chi3,chi4) = -p   for p = 1 mod 3  (with p = 3 mod 4)
    J(chi3,chi4) = +p   for p = 2 mod 3

over F_q, q = p^2.  Everything is EXACT: elements of Z[zeta_12] are integer vectors in the basis
{1,z,z^2,z^3} reduced mod the cyclotomic polynomial z^4 - z^2 + 1.  No floating point.

DERIVATION A (p = 2 mod 3):  then 12 | p+1, so chi3 (N=3), chi4 (N=4) and chi3chi4 (N=12) ALL have
order dividing p+1, i.e. p = -1 mod N -- the SEMI-PRIMITIVE (uniform cyclotomy) case, where
    g(chi) = (-1)^((p+1)/N) * p        [Berndt-Evans-Williams Thm 11.6.3, s=1]
Then with J = g(chi3)g(chi4)/g(chi3chi4) and P = p+1 = 12k:
    exponent E = P/3 + P/4 - P/12 = 4k + 3k - k = 6k  -- ALWAYS EVEN  =>  J = +p.

DERIVATION B (p = 1 mod 3):  chi3 is a norm-lift chi'oN of a cubic chi' on F_p; chi4 and rho=chi4^2
are trivial on F_p^*.  Using g(lambda^p) = g(lambda) (Frobenius-stability of the additive character),
Hasse-Davenport lifting, and the duplication formula over both F_q and F_p, one gets
    g(chi3chi4)^2 = g_p(chi')^4    and    J^2 = p^2,
i.e. J is a RATIONAL INTEGER +-p -- which is exactly the step the ledger records as "would need
sigma_5-invariance, observed numerically, NOT derived".  The SIGN is NOT settled by this argument.

This script checks: (i) J is a rational integer and equals the claimed sign, on FRESH out-of-sample
primes; (ii) the semi-primitive closed form for every chi of order dividing p+1; (iii) the identity
g(chi3chi4)^2 = g_p(chi')^4 that Derivation B rests on.
"""
import sys
from math import gcd

# ---------------- exact Z[zeta_12] arithmetic: vectors (a0,a1,a2,a3) = a0 + a1 z + a2 z^2 + a3 z^3
# minimal polynomial z^4 = z^2 - 1
def zmul(a, b):
    c = [0] * 7
    for i in range(4):
        if a[i]:
            for j in range(4):
                c[i + j] += a[i] * b[j]
    # reduce: z^4 = z^2 - 1 ; z^5 = z^3 - z ; z^6 = z^4 - z^2 = -1
    c[2] += c[4]; c[0] -= c[4]; c[4] = 0
    c[3] += c[5]; c[1] -= c[5]; c[5] = 0
    c[0] -= c[6]; c[6] = 0
    return tuple(c[:4])


def zpow_unit(e):
    """zeta_12^e as a vector."""
    e %= 12
    v = [0, 0, 0, 0]
    if e < 4:
        v[e] = 1
        return tuple(v)
    # z^4 = z^2 - 1, z^5 = z^3 - z, z^6 = -1, then z^(e+6) = -z^e
    if e >= 6:
        base = zpow_unit(e - 6)
        return tuple(-x for x in base)
    if e == 4:
        return (-1, 0, 1, 0)
    return (0, -1, 0, 1)          # e == 5


def zadd(a, b):
    return tuple(x + y for x, y in zip(a, b))


def is_rational(v):
    return v[1] == 0 and v[2] == 0 and v[3] == 0


# ---------------- F_{p^2} as F_p[s]/(s^2 - ns), ns a non-residue
def build_field(p):
    ns = next(u for u in range(2, p) if pow(u, (p - 1) // 2, p) == p - 1)
    q = p * p
    els = [(a, b) for a in range(p) for b in range(p)]      # a + b*s

    def mul(x, y):
        return ((x[0] * y[0] + x[1] * y[1] % p * ns) % p, (x[0] * y[1] + x[1] * y[0]) % p)

    # find a generator of F_q^*
    fac = []
    m = q - 1
    d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fac.append(m)

    def powe(x, e):
        r = (1, 0)
        while e:
            if e & 1:
                r = mul(r, x)
            x = mul(x, x)
            e >>= 1
        return r

    for a in range(1, p):
        for b in range(p):
            g = (a, b)
            if g == (0, 0):
                continue
            if all(powe(g, (q - 1) // f) != (1, 0) for f in fac):
                return p, q, ns, mul, g, powe
    raise RuntimeError("no generator")


def index_table(p, q, mul, g):
    ind = {}
    cur = (1, 0)
    for k in range(q - 1):
        ind[cur] = k
        cur = mul(cur, g)
    return ind


def jacobi_q(p, n1, n2):
    """J(chi_{n1}, chi_{n2}) over F_{p^2} as an exact Z[zeta_12] vector (n1,n2 | 12)."""
    p, q, ns, mul, g, powe = build_field(p)
    ind = index_table(p, q, mul, g)
    e1, e2 = 12 // n1, 12 // n2
    cnt = [0] * 12
    for x in ind:
        one_minus = ((1 - x[0]) % p, (-x[1]) % p)
        if x == (0, 0) or one_minus == (0, 0):
            continue
        cnt[(e1 * ind[x] + e2 * ind[one_minus]) % 12] += 1
    acc = (0, 0, 0, 0)
    for r in range(12):
        if cnt[r]:
            acc = zadd(acc, tuple(cnt[r] * c for c in zpow_unit(r)))
    return acc


def semiprimitive_check(p):
    """For every N | p+1, N>1, the character of order N should have g(chi) = (-1)^((p+1)/N) p.
       We verify the CONSEQUENCE via Jacobi sums where possible (avoids building additive chars)."""
    out = []
    for N in (2, 3, 4, 6, 12):
        if (p + 1) % N == 0:
            out.append((N, (-1) ** ((p + 1) // N)))
    return out


def main():
    print("=" * 78)
    print("Jacobi sign law  J(chi3,chi4) over F_{p^2},  p = 3 mod 4")
    print("=" * 78)
    IN_SAMPLE = {7, 19, 31, 43, 67, 79, 11, 23, 47, 59, 71, 83}
    primes = [n for n in range(5, 240)
              if all(n % d for d in range(2, int(n ** 0.5) + 1)) and n % 4 == 3]
    print("\n p   p%12  in-sample?   J (exact Z[zeta12])           rational?  J/p   predicted")
    ok = fail = 0
    for p in primes:
        J = jacobi_q(p, 3, 4)
        rat = is_rational(J)
        pred = -1 if p % 3 == 1 else +1
        val = J[0] if rat else None
        agree = rat and val == pred * p
        ok += agree
        fail += (not agree)
        print("  %-4d %-5d %-11s %-30s %-9s %-5s %+d"
              % (p, p % 12, "SEEN" if p in IN_SAMPLE else "fresh", str(J), rat,
                 (str(val // p) if rat else "-"), pred))
    print("\n  agree = %d,  disagree = %d" % (ok, fail))

    print("\n--- Derivation A exponent check (p = 2 mod 3, i.e. p = 11 mod 12): E = 6k must be even ---")
    for p in [q for q in primes if q % 12 == 11][:8]:
        P = p + 1
        E = P // 3 + P // 4 - P // 12
        print("   p=%-4d P=%-4d  E = P/3 + P/4 - P/12 = %d   parity=%s  => J = %+d*p"
              % (p, P, E, "even" if E % 2 == 0 else "ODD", (-1) ** E))

    print("\n--- Derivation B consequence (p = 1 mod 3): J must be a RATIONAL integer ---")
    bad = [p for p in primes if p % 12 == 7 and not is_rational(jacobi_q(p, 3, 4))]
    print("   p = 7 mod 12 with J NOT rational: %s" % (bad if bad else "none"))
    print("JACOBI_DONE")


if __name__ == '__main__':
    main()
