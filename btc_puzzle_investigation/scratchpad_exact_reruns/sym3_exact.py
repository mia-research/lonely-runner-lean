# EXACT, no float. Sym^3 perfect-square claim via 6th-root-of-unity exponent arithmetic.
import sympy as sp
from itertools import combinations_with_replacement
from collections import Counter

# 1) Eigenvalue structure, EXACT: N_a/sqrt(p) satisfies s^4+s^2+1. Factor it exactly.
s = sp.symbols('s')
fac = sp.factor(s**4 + s**2 + 1)
print("s^4+s^2+1 factors as:", fac, " (=> roots are primitive 3rd & 6th roots of unity)")
# 6th-root exponents e (u=exp(2*pi*i*e/6)) of the four roots: prim 3rd -> e in {2,4}; prim 6th -> e in {1,5}
exps = [2, 4, 1, 5]           # {zeta3, zeta3bar, zeta6, zeta6bar}
# u^3 sign is EXACT: u^3 = exp(pi*i*e) = (-1)^e
sign_u3 = [(-1)**e for e in exps]
print("root 6th-root exponents e =", exps, "  u^3 = (-1)^e =", sign_u3, " (exact)")

# 2) Sym^3: multisets of 3 roots. Frob^3 eigenvalue sign = product of u^3 signs = (-1)^(sum e_i).
kclass = Counter()      # by k = # of zeta6-type (odd-exponent) factors
sgn = Counter()
for tri in combinations_with_replacement(range(4), 3):
    k = sum(1 for i in tri if exps[i] % 2 == 1)       # zeta6-type = odd exponent
    kclass[k] += 1
    prod_sign = 1
    for i in tri:
        prod_sign *= sign_u3[i]
    sgn[prod_sign] += 1
print("\nSym^3 dim =", sum(kclass.values()), "(expect 20)")
print("collapse classes by k=#zeta6-factors:", dict(sorted(kclass.items())), " (claim 4,6,6,4)")
print("Frob^3 eigenvalue signs:  (+1):", sgn[+1], "  (-1):", sgn[-1], " (each is p^{9/2}*sign)")
ok = (dict(sorted(kclass.items())) == {0:4,1:6,2:6,3:4}) and sgn[+1]==10 and sgn[-1]==10
print("=> char poly of Frob^3 on Sym^3 = (T^2 - p^9)^10 = [ (T^2-p^9)^5 ]^2  PERFECT SQUARE:", ok)
print("   (all arithmetic above is exact integer / symbolic -- no float anywhere)")
