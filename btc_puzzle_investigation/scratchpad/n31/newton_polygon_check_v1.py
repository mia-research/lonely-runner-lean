"""
N31 sub-check: is the claim in RESULT_nonarchimedean_purity_statement_v1.md §2 —
"the Newton polygon of L_a(T) at p has all slopes = 1/2" — true?

Exact integer arithmetic only (CLAUDE.md NO-FLOAT rule). No float anywhere.

Object: E: y^2 = x^3 + 7 over F_p, n = #E(F_p) prime, G a generator, d: E(F_p) -> Z/n.
  V_y(a) = sum_{P != O} chi2(y_P) * zeta_n^{a d(P)}       (an element of Z[zeta_n])
  e1 = -V_y(a) = -f(zeta_n^a)  with  f(X) = sum_j c_j X^j,  c_j = chi2(y_{P_j}) in {-1,0,1}.

The cap chain's char poly (RESULT_n1_cap_reduces_to_one_identity_v1.md §1-2):
  P_a(T) = T^4 - e1 T^3 + e2 T^2 - e3 T + e4,  e4 = p^2, e3 = chi2(-1) p e1, e2 = e1^2 - chi2(-1) p.

Newton polygon at a prime pi | p of Z[zeta_n]:
  v(a4)=0, v(a3)=v(e1), v(a2)=v(e1^2 - chi p), v(a1)=1+v(e1), v(a0)=2.
  If v(e1)=0 then the lower hull is (0,2)->(2,0)->(4,0): root valuations {1,1,0,0}, NOT {1/2 x 4}.

So the claim is refuted for every a as soon as v_pi(e1) = 0 for all pi | p, which holds iff
  p does not divide  N(f(zeta_n)) = Res(Phi_n(X), f(X))   (an exact integer).
All a give Galois conjugates of f(zeta_n), so one norm settles every a.
"""
from sympy import Poly, symbols, resultant, ZZ

X = symbols('X')

def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    r = pow(a, (p - 1) // 2, p)
    return 1 if r == 1 else -1

def curve_points(p, B=7):
    pts = []            # affine points (x, y)
    for x in range(p):
        rhs = (x * x % p * x + B) % p
        for y in range(p):
            if y * y % p == rhs:
                pts.append((x, y))
    return pts

def ec_add(P, Q, p, A=0):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    if P == Q:
        lam = (3 * x1 * x1 + A) * pow(2 * y1, -1, p) % p
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    y3 = (lam * (x1 - x3) - y1) % p
    return (x3, y3)

def run(p):
    pts = curve_points(p)
    n = len(pts) + 1                      # + point at infinity
    G = pts[0]
    # dlog table: c[j] = chi2(y) of the point [j]G ; c[0] = 0 (the point O)
    c = [0] * n
    P = G
    for j in range(1, n):
        c[j] = legendre(P[1], p)
        P = ec_add(P, G, p)
    assert P is None, "order of G is not n -- n not prime or bad generator"
    f = Poly(list(reversed(c)), X, domain=ZZ)          # sum c_j X^j
    Phi = Poly([1] * n, X, domain=ZZ)                  # (X^n-1)/(X-1), n prime
    R = int(resultant(Phi, f))                         # = prod_{a=1}^{n-1} f(zeta^a) = N(e1) up to sign
    vp = 0
    RR = R
    while RR != 0 and RR % p == 0:
        RR //= p; vp += 1
    return dict(p=p, n=n, chi2_minus1=legendre(-1, p),
                nonzero_c=sum(1 for v in c if v != 0),
                zero_c=sum(1 for v in c if v == 0),
                norm=R, v_p_of_norm=vp)

if __name__ == "__main__":
    for p in (43, 67, 79, 127, 163):
        r = run(p)
        print(f"p={r['p']:4d}  n={r['n']:4d}  chi2(-1)={r['chi2_minus1']:+d}  "
              f"#\\{{j: c_j=0\\}}={r['zero_c']}  v_p(N(e1))={r['v_p_of_norm']}  "
              f"=> v_pi(e1)=0 for all a: {r['v_p_of_norm'] == 0}")
        print(f"        N(e1) = {r['norm']}")
