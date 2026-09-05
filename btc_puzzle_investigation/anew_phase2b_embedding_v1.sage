# PHASE 2b -- what the decomposability implies for the cover's own DLP.
# For each m, the A_new Frobenius eigenvalues are sqrt(p)*zeta ; the ORDER of zeta
# bounds the embedding degree of the new part.  Derived from the defining polynomial,
# NOT repeated from any source (project has a logged incident on exactly this).
R.<z> = QQ[]
K.<t> = CyclotomicField(24)
print("m   z^4+m z^2+1 factors over Q      root orders in mu_24     k = lcm(orders)")
for m in (-2,-1,0,1,2):
    f = z^4 + m*z^2 + 1
    orders = []
    for r, e in f.roots(K, multiplicities=True):
        orders += [r.multiplicative_order()]*e
    print("%-3d %-32s %-24s %d" % (m, str(f.factor()), sorted(orders), lcm(orders)))

print()
print("Interpretation, stated as a DERIVATION:")
print("  pi = sqrt(p)*zeta with zeta^k = 1  =>  pi^(2k) = p^k  =>  every eigenvalue of Frob^(2k)")
print("  is the rational integer p^k  =>  the new part's group order divides p^(2k)-1-type")
print("  quantities, i.e. the embedding degree of A_new is bounded by 2k <= 24.")
