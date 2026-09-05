#!/usr/bin/env sage
"""reduce26_signpattern_inspect_v1.sage -- the 21/21 balance is real; what is the actual sign pattern?
Print chi_2(gF)(t) as a function of t and look for ANY structure (linear, multiplicative character,
correlation with chi_2 of small polynomials). The linear/degree-2 searches failed; inspect directly."""
from sage.all import GF, EllipticCurve, ZZ
load("reduce26_signfactoring_v1.sage")   # brings in sign_table, chi2

if __name__ == "__main__":
    p, A, B = 43, 0, 7
    Fp = GF(p)
    E = EllipticCurve(Fp, [A, B]); n = E.order()
    G = next(P for P in E if P.order() == n)
    Rpt = 3*G
    sgn = sign_table(p, A, B, Rpt)
    covered = set(sgn.keys())
    all_t = set(range(p))
    uncovered = sorted(all_t - covered)
    print("R=[3]G. uncovered t-values:", uncovered)
    print("full sign table chi_2(gF)(t) for t=0..%d:" % (p-1))
    row = ""
    for t in range(p):
        if t in sgn:
            row += "+" if sgn[t]==1 else "-"
        else:
            row += "."
        if (t+1) % 22 == 0: row += "\n"
    print(row)
    print("(+ = +1, - = -1, . = uncovered)\n")

    # cross-correlate chi_2(gF) with chi_2(t-a) for each a, and with chi_2(t^2+c), etc.
    # correlation = #{t covered: sgn[t]==chi_2(f(t))}
    def corr(fsign, name):
        m = sum(1 for t in covered if sgn[t] == fsign(t))
        return "%s: %d/%d agree" % (name, m, len(covered))
    print("correlations (42 points; 21 = chance, 42 = perfect):")
    for a in range(p):
        print("  ", corr(lambda t,a=a: chi2((t-a)%p, p), "chi_2(t-%d)" % a))
    # also chi_2 of t (multiplicative character)
    print("  ", corr(lambda t: chi2(t, p), "chi_2(t)"))
    # chi_2(gF) as a multiplicative character of t? t -> sgn[t]. Is sgn[t] = chi_2(t^k) for some k?
    for k in (1,2,3,5,7):
        print("  ", corr(lambda t,k=k: chi2(pow(t,k,p), p), "chi_2(t^%d)" % k))
