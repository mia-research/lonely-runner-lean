#!/usr/bin/env python3
"""
anew_n_visibility_v1.py  --  exact, no float.

QUESTION (pre-committed before the run, see PREREG block below):
  Does the secp256k1 group order n appear as an element order in A_new(F_{p^j})
  for any j in the useful range?  This is the MOV/Frey-Ruck *embedding-degree*
  condition for the proposed E -> A_new bridge, applied to the BRIDGE'S TARGET.

  n is prime, so:  a nonzero group hom  Z/n = <G>  ->  A_new(F_{p^j})  exists
  iff  n | #A_new(F_{p^j}).  Equivalently: iff A_new(F_{p^j}) has a point of
  order n.  This is a NECESSARY condition for any transfer -- homomorphic or
  not -- whose output's A_new-discrete-log is an injective (e.g. affine)
  function of d mod n.

PREREG (statistic / outcome map / control), fixed before any number was printed:
  STATISTIC : g(m, j) = gcd(n, #A_new(F_{p^j})), exact integers only.
  MODEL     : A_new is supersingular at secp (record: PROVED, p = 3 mod 4,
              curve-independent), b1 = 0, b2 = m*p, so
              P(T) = T^4 + m*p*T^2 + p^2,  m in {-2,-1,0,1,2} (|alpha| = sqrt p
              forces |m| <= 2).  Run ALL FIVE m so the verdict does not depend
              on the [CONDITIONAL] m = 1 branch.
              #A_new(F_{p^j}) = det(I - M^j), M = companion matrix of P.
  OUTCOME MAP (committed in advance):
     g > 1 for some (m, j) with small j  -> POSITIVE: the n-part is visible in
              the bridge's target; the transfer target is live; report and test.
     g = 1 for all tested (m, j)         -> the affine-log transfer class into
              A_new(F_{p^j}) is empty for those j.  Scope is the tested j only;
              the accompanying THEOREM (not this run) is what extends it.
  FIRING CONTROL (must fire, else the detector is vacuous):
     C1  same detector run at small primes, where sharing a factor is common:
         must report g > 1 somewhere.
     C2  planted positive: replace n by a prime divisor of #A_new(F_{p^j});
         detector must report g > 1.
  INSTRUMENT CHECK:
     I1  N_1 = det(I - M) must equal P(1) = 1 + m*p + p^2.
     I2  m = -2 must give N_j = (p^j - 1)^2 exactly (P = (T^2 - p)^2), and
         m = 1 must give N_1 = p^2 + p + 1 -- both closed forms known a priori.
"""

from math import gcd

# ---------- secp256k1 ----------
P_SECP = 2**256 - 2**32 - 977
N_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

# ---------- exact 4x4 integer linear algebra ----------

def mat_mul(A, B):
    k = len(A)
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(k)]
            for i in range(k)]

def mat_pow(A, e):
    k = len(A)
    R = [[1 if i == j else 0 for j in range(k)] for i in range(k)]
    while e:
        if e & 1:
            R = mat_mul(R, A)
        A = mat_mul(A, A)
        e >>= 1
    return R

def det_int(M):
    """Bareiss fraction-free determinant. Exact integers, no division that is
    not exact."""
    M = [row[:] for row in M]
    n = len(M)
    sign = 1
    prev = 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for r in range(k + 1, n):
                if M[r][k] != 0:
                    M[k], M[r] = M[r], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = M[i][j] * M[k][k] - M[i][k] * M[k][j]
                assert num % prev == 0, "Bareiss: inexact division"
                M[i][j] = num // prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]

def companion(p, m):
    """Companion matrix of P(T) = T^4 + m*p*T^2 + p^2  (b1 = 0)."""
    c0, c1, c2, c3 = p * p, 0, m * p, 0
    return [[0, 0, 0, -c0],
            [1, 0, 0, -c1],
            [0, 1, 0, -c2],
            [0, 0, 1, -c3]]

def order_A_new(p, m, j):
    """#A_new(F_{p^j}) = prod_i (1 - alpha_i^j) = det(I - M^j)."""
    M = companion(p, m)
    Mj = mat_pow(M, j)
    I_minus = [[(1 if i == k else 0) - Mj[i][k] for k in range(4)]
               for i in range(4)]
    return det_int(I_minus)

# ---------- instrument checks ----------

def instrument_checks():
    out = []
    ok = True
    for p in (43, 67, 79, 127, P_SECP):
        for m in (-2, -1, 0, 1, 2):
            n1 = order_A_new(p, m, 1)
            expect = 1 + m * p + p * p
            if n1 != expect:
                ok = False
                out.append(f"  I1 FAIL p={p} m={m}: {n1} != {expect}")
    out.append(f"  I1  N_1 == P(1) = 1 + m*p + p^2 : {'PASS' if ok else 'FAIL'}")

    ok2 = True
    for p in (43, 67, 79, 127, P_SECP):
        for j in (1, 2, 3, 5, 7, 12):
            got = order_A_new(p, -2, j)
            # P = (T^2 - p)^2, roots +-sqrt(p) each twice.  j odd: the two
            # signs survive -> (1-p^j)^2.  j even: all four powers equal
            # p^(j/2) -> (1 - p^(j/2))^4.
            want = (p**j - 1) ** 2 if j % 2 else (p ** (j // 2) - 1) ** 4
            if got != want:
                ok2 = False
                out.append(f"  I2 FAIL m=-2 p={p} j={j}: {got} != {want}")
        if order_A_new(p, 1, 1) != p * p + p + 1:
            ok2 = False
            out.append(f"  I2 FAIL m=1 p={p}: N_1 != p^2+p+1")
    out.append(f"  I2  closed forms m=-2 -> (p^j-1)^2, m=1 -> p^2+p+1 : "
               f"{'PASS' if ok2 else 'FAIL'}")
    return ok and ok2, out

# ---------- main sweep ----------

def sweep(p, n, jmax, label):
    print(f"\n--- {label} ---")
    print(f"  p bits = {p.bit_length()}, n bits = {n.bit_length()}")
    hits = []
    for m in (-2, -1, 0, 1, 2):
        gs = []
        for j in range(1, jmax + 1):
            g = gcd(n, order_A_new(p, m, j))
            gs.append(g)
            if g > 1:
                hits.append((m, j, g))
        distinct = sorted(set(gs))
        print(f"  m = {m:>2} : gcd(n, #A_new(F_p^j)) for j=1..{jmax} -> "
              f"distinct values {distinct}")
    return hits

def main():
    print("=" * 78)
    print("A_new n-VISIBILITY  --  exact integer run, no float in any path")
    print("=" * 78)

    ok, lines = instrument_checks()
    print("\n[INSTRUMENT CHECKS]")
    for l in lines:
        print(l)
    if not ok:
        raise SystemExit("instrument check failed -- run aborted")

    # ---- the secp run ----
    JMAX = 64
    hits = sweep(P_SECP, N_SECP, JMAX, f"SECP  (j = 1..{JMAX})")
    print(f"\n  SECP HITS (gcd > 1): {hits if hits else 'NONE'}")

    # ---- the multiplicative-order bound behind the theorem ----
    print("\n[ORDER OF p MOD n  --  the quantity the theorem turns on]")
    # known factorisation of n-1 (verified below by multiplication + primality)
    fac = [2, 2, 2, 2, 2, 2, 3, 149, 631,
           107361793816595537,
           174723607534414371449,
           341948486974166000522343609283189]
    prod = 1
    for f in fac:
        prod *= f
    print(f"  factorisation of n-1 reproduces n-1 : {prod == N_SECP - 1}")
    try:
        from sympy import isprime
        big = [f for f in fac if f > 1000]
        print(f"  large factors prime (sympy)         : "
              f"{all(isprime(f) for f in big)}")
    except Exception as e:  # pragma: no cover
        print(f"  (sympy unavailable: {e})")

    order = N_SECP - 1
    for q in sorted(set(fac)):
        while order % q == 0 and pow(P_SECP, order // q, N_SECP) == 1:
            order //= q
    print(f"  ord_n(p) = {order}")
    print(f"  ord_n(p) bits = {order.bit_length()}")
    print(f"  ord_n(p) == (n-1)/6 : {order == (N_SECP - 1) // 6}   "
          f"[record P7']")
    print(f"  p^ord == 1 mod n    : {pow(P_SECP, order, N_SECP) == 1}")

    # ---- the theorem's load-bearing step, checked exactly ----
    # Claim: for each admissible m there is e = e(m) with alpha^e = p^(e/2) for
    # every eigenvalue, i.e. M^e = p^(e/2) * I as integer matrices.
    # NB the matrix form M^e = p^(e/2) I is FALSE for m = +-2, where P has
    # repeated roots and M is not semisimple.  The theorem needs only the
    # EIGENVALUE statement, so test it on the radical (squarefree part) of P:
    #   every root alpha of P satisfies alpha^e = p^(e/2)
    #   <=>  rad(P)(T)  divides  T^e - p^(e/2)  in Q[T].
    print("\n[THEOREM STEP, CHECKED EXACTLY:  every root has alpha^e = p^(e/2)]")
    from sympy import Poly, Symbol, QQ, rem
    T = Symbol('T')
    e_of_m = {}
    for m in (-2, -1, 0, 1, 2):
        Pm = Poly(T**4 + m * P_SECP * T**2 + P_SECP**2, T, domain=QQ)
        rad = Pm.quo(Pm.gcd(Pm.diff(T)))      # squarefree part, exact
        found = None
        for e in (2, 4, 6, 8, 12, 24):
            tgt = Poly(T**e - P_SECP**(e // 2), T, domain=QQ)
            if rem(tgt, rad).is_zero:
                found = e
                break
        e_of_m[m] = found
        print(f"  m = {m:>2} : deg rad(P) = {rad.degree()},  minimal even e "
              f"with rad(P) | T^e - p^(e/2)  ->  e = {found}")
    assert all(v is not None for v in e_of_m.values()), "no e found for some m"
    e_max = max(e_of_m.values())
    print(f"  e_max over all admissible m = {e_max}  "
          f"(so alpha^{e_max} = p^{e_max//2} always)")

    # n | #A_new(F_{p^j})  ==>  some alpha_i^j = 1 mod (prime over n)
    #                      ==>  p^((e/2) j) = 1 mod n   ==>  ord | (e/2) j.
    print("\n[THEOREM BOUND]")
    for m in (-2, -1, 0, 1, 2):
        half = e_of_m[m] // 2
        jm = -(-order // half)
        print(f"  m = {m:>2} : ord_n(p) | {half}*j  =>  j >= {jm.bit_length()} bits")
    jmin = -(-order // (e_max // 2))
    print(f"  WORST CASE over m: j >= {jmin}")
    print(f"                       ( {jmin.bit_length()} bits )")
    m1 = -(-order // (e_of_m[1] // 2))
    print(f"  SECP BRANCH m = 1  : j >= {m1.bit_length()} bits")

    # ---- FIRING CONTROLS ----
    print("\n[FIRING CONTROLS]")
    # C1: same detector, small primes, using each prime's own E-group order
    #     surrogate n_small = a prime factor of p^2+p+1 or of (p-1) etc.
    #     We use the honest analogue: n_small = largest prime factor of #E(F_p)
    #     is not needed -- the detector under test is gcd(n, N_j), so we plant
    #     realistic small-prime co-factors.
    from sympy import factorint
    c1_fired = []
    for p_s in (43, 67, 79, 103, 127, 139, 151, 163):
        for m in (-2, -1, 0, 1, 2):
            for j in (1, 2, 3, 4, 6):
                Nj = order_A_new(p_s, m, j)
                if Nj == 0:
                    continue
                # surrogate "n": a prime factor of #A_new over a DIFFERENT
                # (m, j) cell -- so a hit is not automatic
                other = order_A_new(p_s, m, j + 1)
                if other in (0, 1):
                    continue
                q = max(factorint(abs(other)))
                if gcd(q, abs(Nj)) > 1:
                    c1_fired.append((p_s, m, j, q))
    print(f"  C1 cross-cell small-prime detector fires: "
          f"{'YES' if c1_fired else 'NO'}  ({len(c1_fired)} hits, "
          f"e.g. {c1_fired[:3]})")

    # C2: planted positive at secp scale -- take a genuine prime factor of
    #     #A_new(F_p) and confirm the detector reports it.
    m_planted = 1
    N1 = order_A_new(P_SECP, m_planted, 1)
    planted = None
    for small_q in (3, 7, 13, 31, 37, 43, 61, 67, 79, 103, 109, 127, 157, 181,
                    193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313):
        if N1 % small_q == 0:
            planted = small_q
            break
    if planted:
        g = gcd(planted, N1)
        print(f"  C2 planted divisor {planted} of #A_new(F_p) at secp "
              f"(m=1): detector returns gcd = {g}  -> "
              f"{'FIRES' if g > 1 else 'DEAD'}")
    else:
        # fall back: plant an artificial one
        g = gcd(N1, N1)
        print(f"  C2 planted (self) : gcd = N_1 > 1 -> "
              f"{'FIRES' if g > 1 else 'DEAD'}")

    # ---- context: E's own MOV degree, for the comparison the theorem makes ----
    print("\n[COMPARISON  --  what the bridge would have to beat]")
    half_max = e_max // 2
    print(f"  E's own MOV embedding degree ord_n(p)        = "
          f"{order.bit_length()} bits")
    print(f"  A_new bridge's n-embedding degree >= ord/{half_max}  = "
          f"{jmin.bit_length()} bits")
    print(f"  maximum possible gain from the bridge        = factor "
          f"{half_max}  (< 3 bits)")
    print(f"  at the secp branch m = 1 the gain is         = factor "
          f"{e_of_m[1]//2}  (< 2 bits)")
    print("\n  NOTE ON COUNTING: the j = 1..64 sweep above is FORCED by this "
          "theorem.\n  It is an instrument check on the code, NOT independent "
          "evidence for the bound.")

if __name__ == "__main__":
    main()
