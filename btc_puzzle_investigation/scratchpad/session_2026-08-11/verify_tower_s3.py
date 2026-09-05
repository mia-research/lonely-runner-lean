import sympy as sp
from sympy import GF, Poly, symbols, factor_list, discriminant

T = symbols('T')

P40 = (T**40 + 1170*T**38 + 627551*T**36 + 205398058*T**34 + 46054301751*T**32
       + 7525745599708*T**30 + 930544562912690*T**28 + 89193503494507584*T**26
       + 6733013957448634368*T**24 + 404312215797268611072*T**22
       + 19421056698543979364352*T**20 + 747573287009149450715136*T**18
       + 23018834850739337597812736*T**16 + 563824517201032512586907648*T**14
       + 10876391218556210258301157376*T**12 + 162642517922366262595960176640*T**10
       + 1840312894595683715993231687680*T**8 + 15175908913122086617876193607680*T**6
       + 85732268460455519833095801929728*T**4 + 295541220280992653217175745593344*T**2
       + 467056167777397617695922357010432)

poly = Poly(P40, T)
print("degree:", poly.degree())
print("all coeffs integer:", all(c==int(c) for c in poly.all_coeffs()))

doc_claims = {3:[20,20], 11:[4,4,16,16], 19:[2,2,18,18], 23:[4,36], 53:[10,30]}

for ell, claim in doc_claims.items():
    pl = Poly(P40, T, modulus=ell)
    fl = pl.factor_list()
    # degrees of irreducible factors with multiplicity
    degs=[]
    for fac,m in fl[1]:
        degs += [Poly(fac,T,modulus=ell).degree()]*m
    degs_sorted = sorted(degs)
    claim_sorted = sorted(claim)
    # separability check: any repeated factor?
    mults = [m for fac,m in fl[1]]
    separable = all(m==1 for m in mults)
    match = (degs_sorted == claim_sorted)
    print(f"\nell={ell}: factor degrees = {sorted(degs, reverse=True)}  (doc claims {claim})")
    print(f"        separable mod {ell}: {separable}   cycle-type match: {match}")

# Even-permutation / A_40 check: a permutation is even iff (number of even-length cycles) is even.
print("\n--- Parity check (G subset of A_40?) ---")
for ell, claim in doc_claims.items():
    pl = Poly(P40, T, modulus=ell)
    fl = pl.factor_list()
    degs=[]
    for fac,m in fl[1]:
        degs += [Poly(fac,T,modulus=ell).degree()]*m
    # sign of permutation = product of (-1)^(len-1) over cycles
    n_even_cycles = sum(1 for d in degs if d%2==0)
    parity = "even" if n_even_cycles%2==0 else "ODD"
    print(f"  ell={ell}: cycle degrees {sorted(degs,reverse=True)}, #even-length cycles={n_even_cycles} -> {parity} permutation")
