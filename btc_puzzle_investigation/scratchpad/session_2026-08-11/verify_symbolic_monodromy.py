import sympy as sp
from itertools import combinations_with_replacement
from collections import Counter

# The 4 Frobenius roots with the 120-degree phase lock:
#   roots = {alpha, alphabar, beta=zeta*alpha, betabar=zeta^2*alphabar}
# Represent each root as a monomial in (alpha, alphabar, zeta) tracked by exponent tuple
# (a, b, c) meaning alpha^a * alphabar^b * zeta^c,  with zeta^3 = 1.

# root list as (a_exp, b_exp, zeta_exp)
roots = [
    (1, 0, 0),   # alpha
    (0, 1, 0),   # alphabar
    (1, 0, 1),   # zeta * alpha       (= beta)
    (0, 1, 2),   # zeta^2 * alphabar  (= betabar)
]
labels = ['a', 'ab', 'z*a', 'z^2*ab']

# ---- Sym^3: all combinations-with-replacement of 3 roots ----
triples = list(combinations_with_replacement(range(4), 3))
print(f"Number of Sym^3 basis elements: {len(triples)}  (expected C(6,3)=20)")

# raw product exponents (a,b,c mod 3 for zeta)
raw = []
for (i,j,k) in triples:
    a = roots[i][0]+roots[j][0]+roots[k][0]
    b = roots[i][1]+roots[j][1]+roots[k][1]
    c = (roots[i][2]+roots[j][2]+roots[k][2]) % 3
    raw.append((a,b,c))

print("\n--- §1: RAW (pre-base-change) 20 roots, grouped by (alpha-exp, alphabar-exp, zeta-exp) ---")
raw_counter = Counter(raw)
for key in sorted(raw_counter):
    a,b,c = key
    print(f"  alpha^{a} alphabar^{b} zeta^{c}  : multiplicity {raw_counter[key]}")

# Check the document's §1 claim:
#  degree-8 block (mult 2 each): {alpha^3, alphabar^3, alpha*alphabar^2, alpha^2*alphabar} with zeta^0
#  degree-12 block: those 4 base monomials times zeta^{+-1}
print("\n  Document §1 claims a degree-8 block (4 monomials, each mult 2, zeta^0):")
deg8_claim = [(3,0,0),(0,3,0),(1,2,0),(2,1,0)]
for m in deg8_claim:
    print(f"    {m}: actual mult = {raw_counter.get(m,0)}  (claimed 2)")
print("  Document §1 claims a degree-12 block: same 4 base monomials times zeta^{+-1}:")
deg12_claim = []
for (a,b,_) in deg8_claim:
    deg12_claim += [(a,b,1),(a,b,2)]
for m in deg12_claim:
    print(f"    {m}: actual mult = {raw_counter.get(m,0)}")

# ---- Base change to F_{p^3}: CUBE each of the 20 roots ----
# cubing:  alpha^a alphabar^b zeta^c  ->  alpha^{3a} alphabar^{3b} zeta^{3c} = alpha^{3a} alphabar^{3b}
cubed = [(3*a, 3*b) for (a,b,c) in raw]   # zeta^{3c}=1 always
print("\n--- §2: CUBED (base-changed) 20 roots, grouped by (alpha-exp, alphabar-exp) ---")
cubed_counter = Counter(cubed)
for key in sorted(cubed_counter, reverse=True):
    a,b = key
    print(f"  alpha^{a} alphabar^{b}  : multiplicity {cubed_counter[key]}")

mults = sorted(cubed_counter.values())
print(f"\n  Distinct cubed values: {len(cubed_counter)}  (document claims 4)")
print(f"  Multiplicities: {sorted(cubed_counter.values(), reverse=True)}  (document claims 4,4,6,6)")
all_even = all(m % 2 == 0 for m in cubed_counter.values())
print(f"  All multiplicities even? {all_even}  ->  perfect square {'FORCED' if all_even else 'NOT forced'}")

# ---- Independent numeric confirmation with concrete alpha, alphabar ----
print("\n--- Independent NUMERIC check with concrete alpha, alphabar, zeta ---")
import cmath
alpha = 2.0 + 3.0j
alphabar = 2.0 - 3.0j   # complex conjugate, as for a real Frobenius
zeta = cmath.exp(2j*cmath.pi/3)
rts = [alpha, alphabar, zeta*alpha, zeta**2*alphabar]
prods = []
for (i,j,k) in triples:
    prods.append(rts[i]*rts[j]*rts[k])
cubed_num = [p**3 for p in prods]
# cluster by closeness
clusters = []
for v in cubed_num:
    placed = False
    for cl in clusters:
        if abs(cl[0]-v) < 1e-6*max(1,abs(v)):
            cl.append(v); placed=True; break
    if not placed:
        clusters.append([v])
print(f"  Numeric: {len(clusters)} distinct cubed values, multiplicities {sorted([len(c) for c in clusters], reverse=True)}")

# Build the actual degree-20 char poly numerically and test perfect-square-ness
T = sp.symbols('T')
poly = sp.prod([(1 - sp.nsimplify(v.real, rational=False) ) for v in []])  # placeholder
# Instead: form poly with numeric complex coeffs, then check if sqrt has real/consistent coeffs
import numpy as np
# characteristic poly with roots = cubed_num (reciprocal-root convention prod(1 - r T))
coeffs = np.poly([1.0/v for v in cubed_num])  # np.poly gives prod(x - root); we just need factorization structure
# Simpler: a poly is a perfect square iff each root multiplicity is even -> already shown.
print(f"  (Perfect-square-ness already determined by even multiplicities above.)")
