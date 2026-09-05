"""
N31: citation-free exact purity check, widened.

Reproduces + extends RESULT_item6_D2_and_purity_v1.md sec.3.  Exact integers only (no float).

R(T) = prod_{a=1}^{n-1} P_a(T) = Res_X(Phi_n(X), P(X,T))  in  Z[T],  Galois-stable,
so its root set is closed under EVERY embedding of the splitting field.  Purity at every
embedding  <=>  every root of R has |alpha| = sqrt(p).

Test (exact, no float, no citation):
  1. R(T) = T^m * Q(T + p/T)  for some Q in Z[S]   (the p-reciprocal functional equation)
  2. Q squarefree part has ALL roots real            (Sturm count == degree)
  3. every real root x satisfies x^2 <= 4p           (Sturm count of Qhat(v)=Res_S(Q,v-S^2)
                                                      on (4p, oo) is 0 -- INTEGER endpoint)
(1)+(2)+(3)  <=>  all roots of R on the circle |T| = sqrt(p).
"""
import sys, time
from sympy import Poly, symbols, resultant, ZZ, QQ, div, degree

X, T, S, V = symbols('X T S V')

def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

def ec_add(P, Q, p):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    if P == Q: lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
    else:      lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)

def chi_coeffs(p, B=7):
    pts = [(x, y) for x in range(p) for y in range(p)
           if y * y % p == (x * x % p * x + B) % p]
    n = len(pts) + 1
    G = pts[0]; c = [0] * n; P = G
    for j in range(1, n):
        c[j] = legendre(P[1], p); P = ec_add(P, G, p)
    assert P is None, "G is not of order n"
    return n, c

def sturm_real_root_count(q, gen):
    """number of DISTINCT real roots of squarefree q (exact, rational Sturm)."""
    return q.count_roots()

def run(p, verbose=True):
    t0 = time.time()
    n, c = chi_coeffs(p)
    chi = legendre(-1, p)
    # e1(a) = -f(zeta^a);  E1(X) = -f(X)
    E1 = Poly([-v for v in reversed(c)], X, domain=ZZ)
    Phi = Poly([1] * n, X, domain=ZZ)                 # (X^n-1)/(X-1), n prime
    E1 = E1.rem(Phi)
    # P(X,T) = T^4 - E1 T^3 + (E1^2 - chi p) T^2 - chi p E1 T + p^2
    PXT = Poly(T**4, T, X, domain=ZZ) \
        - Poly(E1.as_expr(), T, X, domain=ZZ) * Poly(T**3, T, X, domain=ZZ) \
        + (Poly(E1.as_expr()**2, T, X, domain=ZZ) - Poly(chi*p, T, X, domain=ZZ)) * Poly(T**2, T, X, domain=ZZ) \
        - Poly(chi*p, T, X, domain=ZZ) * Poly(E1.as_expr(), T, X, domain=ZZ) * Poly(T, T, X, domain=ZZ) \
        + Poly(p**2, T, X, domain=ZZ)
    R = Poly(resultant(Phi.as_expr(), PXT.as_expr(), X), T, domain=ZZ)
    d = R.degree()
    # step 1: R(T) = T^m Q(T + p/T),  m = d/2
    m = d // 2
    assert d % 2 == 0
    Qc = []           # build Q by repeated division: strip highest power of (T^2+p) style
    # substitution-free: write R = sum r_i T^i; solve for Q coeffs by matching, using
    # the basis  T^m * (T + p/T)^k  = sum_j C(k,j) p^j T^{m+k-2j}
    from sympy import binomial
    r = [R.coeff_monomial(T**i) for i in range(d + 1)]
    Qcoef = [0] * (m + 1)
    rr = list(r)
    for k in range(m, -1, -1):
        lead = rr[m + k]
        Qcoef[k] = lead
        if lead:
            for j in range(0, k + 1):
                rr[m + k - 2 * j] -= lead * binomial(k, j) * p**j
    ok_fe = all(v == 0 for v in rr)
    Q = Poly(list(reversed(Qcoef)), S, domain=ZZ)
    Qsf = Q.quo(Q.gcd(Q.diff(S)))                     # squarefree part
    nreal = Qsf.count_roots()
    all_real = (nreal == Qsf.degree())
    # step 3: Qhat(V) = Res_S(Qsf, V - S^2); roots are the x_i^2
    Qhat = Poly(resultant(Qsf.as_expr(), V - S**2, S), V, domain=ZZ)
    Qhat = Qhat.quo(Qhat.gcd(Qhat.diff(V)))
    above = Qhat.count_roots(inf=4 * p + 1, sup=None) if Qhat.degree() > 0 else 0
    # count on (4p, oo): use exact rational endpoint 4p (roots ARE <= 4p iff none in (4p,oo))
    above = Qhat.count_roots(inf=QQ(4 * p), sup=None) - (1 if Qhat.eval(4 * p) == 0 else 0)
    verdict = ok_fe and all_real and above == 0
    dt = time.time() - t0
    if verbose:
        print(f"p={p:5d} n={n:5d} chi2(-1)={chi:+d} degR={d:5d} degQ={Q.degree():5d} "
              f"degQsf={Qsf.degree():5d} | FE={ok_fe} allreal={all_real} "
              f"roots_beyond_4p={above} | PURE={verdict} | {dt:.1f}s")
    return verdict

if __name__ == "__main__":
    ps = [int(a) for a in sys.argv[1:]] or [43, 67, 79, 127]
    for p in ps:
        run(p)
