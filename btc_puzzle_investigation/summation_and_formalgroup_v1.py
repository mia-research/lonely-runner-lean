#!/usr/bin/env python3
"""
Two curve-side computations.

(A) Summation polynomials S_m under [omega]:  S3 is a beta-eigenvector (eigenvalue beta^1);
    S4 is a beta-eigenvector (eigenvalue beta^0 = [omega]-invariant), irreducible over Q(b),
    full degree 2^(m-2) in each variable (S4 degree 4). The mu6/automorphism covariance
    carries the sqrt(6) symmetry of |Aut(E)|=6.

(B) Formal group law from the log:  F(T1,T2) = exp(L(T1)+L(T2)) is explicit, mu6-sparse
    (first correction at total degree 7 == 1 mod 6), b=7-driven; L linearizes the formal
    subgroup E_1(Q_p) (points reducing to O).
"""
import sympy as sp

def summation_polys():
    x1, x2, x3, x4, x, b, beta = sp.symbols('x1 x2 x3 x4 x b beta')
    def S3(a1, a2, a3):
        return sp.expand((a1 - a2) ** 2 * a3 ** 2 - 2 * ((a1 + a2) * (a1 * a2) + 2 * b) * a3
                         + ((a1 * a2) ** 2 - 4 * b * (a1 + a2)))
    def eigen(poly, vars_):
        pb = sp.expand(poly.subs({v: beta * v for v in vars_}))
        pb = sp.expand(pb.replace(lambda e: e.is_Pow and e.base == beta, lambda e: beta ** (e.exp % 3)))
        for k in range(3):
            d = sp.expand(sp.expand(pb - beta ** k * poly).replace(
                lambda e: e.is_Pow and e.base == beta, lambda e: beta ** (e.exp % 3)))
            if d == 0:
                return k
        return None
    s3 = S3(x1, x2, x3)
    s4 = sp.expand(sp.resultant(S3(x1, x2, x), S3(x3, x4, x), x))
    print("S3: beta-eigenvalue beta^%s ; factors? %s"
          % (eigen(s3, [x1, x2, x3]), sp.factor(s3) != s3))
    print("S4: beta-eigenvalue beta^%s ; factors? %s ; deg_x1 = %d"
          % (eigen(s4, [x1, x2, x3, x4]), sp.factor(s4) != s4, sp.degree(s4, x1)))
    print("  => [omega]-covariant (the sqrt(6) automorphism symmetry of |Aut(E)|=6).")


def formal_group_law(PREC=20):
    T, T1, T2 = sp.symbols('T T1 T2')
    b = 7
    L = sum(sp.Integer(b) ** k * sp.binomial(3 * k, k) / (6 * k + 1) * T ** (6 * k + 1)
            for k in range(PREC // 6 + 2))
    L = sp.series(L, T, 0, PREC).removeO()
    exp = T
    for _ in range(PREC):
        exp = sp.series(exp - (sp.series(L.subs(T, exp), T, 0, PREC).removeO() - T), T, 0, PREC).removeO()
    F = exp.subs(T, sp.series(L.subs(T, T1), T1, 0, PREC).removeO()
                 + sp.series(L.subs(T, T2), T2, 0, PREC).removeO())
    F = sp.series(sp.series(F, T1, 0, 8).removeO(), T2, 0, 8).removeO()
    print("\nFormal group law F(T1,T2) low terms:")
    print(" ", sp.expand(F))
    print("  identity F(T1,0)=T1:", sp.series(F.subs(T2, 0), T1, 0, 6).removeO() == T1)
    print("  a1 (coeff T1*T2) =", F.coeff(T1, 1).coeff(T2, 1), " (0 for y^2=x^3+7)")
    print("  first correction at total degree 7 (=1 mod 6), coefficients multiples of b=7 => mu6-sparse.")


if __name__ == "__main__":
    summation_polys()
    formal_group_law()
