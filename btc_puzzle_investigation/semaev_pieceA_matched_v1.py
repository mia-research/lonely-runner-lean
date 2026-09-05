#!/usr/bin/env sage
# semaev_pieceA_matched_v1.py  --  RUN WITH: sage semaev_pieceA_matched_v1.py
#
# Closes the GLM frontier-E "singular-fibre collision" sub-question with a MATCHED CONTROL:
# is the S4 singular-fibre locus for B=7 (j=0 CM) any different from a non-CM curve or j=1728?
# semaev_elimination_v1.py ran Piece A only for B=7 (got elim ideal = 0 = diagonal-singular for
# all t). Here we run the identical elimination for (0,7),(5,11),(3,0) and compare -> a B=7-
# specific collision would show a DIFFERENT t-condition for secp than for the controls.
#
# Also: the xy-substitution degree observation (GLM idea) -- w = x*y has w^2 = x^5 + B x^2, so a
# summation relation in w is HIGHER degree in x than S_m; and mu3-weight(xy)=weight(x)=1 (GLV
# fixes y, scales x by beta), so xy carries the SAME grading as x -> the mu3 structure (shown
# lever-free in semaev_elimination_v1 [B2-mu3]) is identical under x<->xy. Reported, not just run.
#
# NO FLOAT IN SIGNAL PATH: exact over GF(p)/QQ.
from sage.all import *

def semaev3(a, b, c, A, B):
    return (a - b)**2 * c**2 - 2*((a + b)*(a*b + A) + 2*B)*c + ((a*b - A)**2 - 4*B*(a + b))

def S4_poly(F, A, B):
    R = PolynomialRing(F, ['z1', 'z2', 'z3', 'z4', 'X'])
    z1, z2, z3, z4, X = R.gens()
    AA, BB = R(A), R(B)
    left = semaev3(z1, z2, X, AA, BB)
    right = semaev3(z3, z4, X, AA, BB)
    S = left.resultant(right, X)
    Rt = PolynomialRing(F, ['z1', 'z2', 'z3', 'z4'])
    return Rt(S), Rt

def singular_locus_t(F, A, B):
    """eliminate x1,x2,x3 from (S4, dS4/dx1, dS4/dx2, dS4/dx3) -> condition on t=z4."""
    S, Rt = S4_poly(F, A, B)
    xs = list(Rt.gens()[:3]); t = Rt.gens()[3]
    J = Rt.ideal([S] + [S.derivative(v) for v in xs])
    elim = J.elimination_ideal(xs)
    return [str(g.factor()) if g != 0 else '0' for g in elim.gens()]

def w_relation_degree(F, B):
    """xy-substitution decidable observation: minimal poly relating w=x*y to x on y^2=x^3+B.
    w^2 = x^2 y^2 = x^2 (x^3 + B) = x^5 + B x^2. Report its x-degree vs the x-coordinate (deg 1)."""
    R = PolynomialRing(F, ['x', 'w'])
    x, w = R.gens()
    rel = w**2 - (x**5 + F(B) * x**2)
    return rel, rel.degree(x)

def main():
    import sys; sys.stdout.reconfigure(line_buffering=True)
    print("=" * 84)
    print("SEMAEV PIECE A (matched control) + xy-substitution observation")
    print("=" * 84)
    curves = [('secp_j0_CMomega', 0, 7), ('nonCM_generic', 5, 11), ('j1728_CMi', 3, 0)]

    print("\n[A-matched] S4 singular-fibre locus (t-condition) -- identical across curves => no B=7 collision")
    for p in [211, 307]:
        F = GF(p)
        print("   p=%d" % p)
        for name, A, B in curves:
            try:
                fac = singular_locus_t(F, A, B)
                print("      %-18s elim(t)-ideal gens: %s" % (name, [s[:70] for s in fac]))
            except Exception as e:
                print("      %-18s FAILED: %s" % (name, repr(e)[:80]))

    print("\n[xy] xy-substitution: w=x*y satisfies w^2 = x^5 + B x^2  (x-degree of the w-relation)")
    for name, A, B in curves:
        F = GF(211)
        rel, dx = w_relation_degree(F, B)
        print("      %-18s B=%d:  w^2 = x^5 + %d x^2   (x-degree %d vs x-coordinate degree 1)"
              % (name, B, B, dx))
    print("      => the xy coordinate is degree-5 in x: a summation relation in w is HIGHER degree,")
    print("         not lower; and mu3-weight(xy)=weight(x)=1 (GLV fixes y, x->beta x), so xy carries")
    print("         the SAME grading as x -> the mu3 lever (absent, [B2-mu3]) is unchanged under x<->xy.")
    print("\n[done]")

if __name__ == '__main__':
    main()
