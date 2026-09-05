import sympy as sp

T, Y = sp.symbols('T Y')
w = sp.Rational(-1,2) + sp.sqrt(-3)/2   # primitive cube root of unity: w^2+w+1=0
w2 = sp.conjugate(w)

print("Sanity: w^2 + w + 1 =", sp.simplify(w**2 + w + 1))
print("Sanity: w^3 =", sp.simplify(w**3))
print()

# ============================================================
# §2.2 IDEA: irreducible-over-Q L-poly splits over Q(w) into
#           conjugate quadratics of the STATED form.
# ============================================================
print("=== §2.2: split over Q(w) into conjugate quadratics ===")

# a=2: L = 169T^4 + 78T^3 + 23T^2 + 6T + 1
#       claimed = (13T^2 - 6w T + w^2)(13T^2 - 6w^2 T + w)
L_a2 = 169*T**4 + 78*T**3 + 23*T**2 + 6*T + 1
claim_a2 = (13*T**2 - 6*w*T + w**2)*(13*T**2 - 6*w2*T + w)
diff_a2 = sp.expand(L_a2 - claim_a2)
diff_a2 = sp.simplify(diff_a2)
print(f"  a=2: L - claimed_product = {diff_a2}   ->  {'EXACT MATCH' if diff_a2==0 else 'MISMATCH'}")

# a=3: L = 169T^4 - 52T^3 + 3T^2 - 4T + 1
#       claimed = (13T^2 + 4w^2 T + w)(13T^2 + 4w T + w^2)
L_a3 = 169*T**4 - 52*T**3 + 3*T**2 - 4*T + 1
claim_a3 = (13*T**2 + 4*w2*T + w)*(13*T**2 + 4*w*T + w2)
diff_a3 = sp.simplify(sp.expand(L_a3 - claim_a3))
print(f"  a=3: L - claimed_product = {diff_a3}   ->  {'EXACT MATCH' if diff_a3==0 else 'MISMATCH'}")

# Independent: verify the two quadratic factors are genuinely CONJUGATE over Q(w)
# (i.e. swapping w<->w^2 maps one factor to the other)
f1_a2 = 13*T**2 - 6*w*T + w**2
f1_a2_conj = f1_a2.subs(w, w2)  # apply Galois conjugation w -> w^2
f2_a2 = 13*T**2 - 6*w2*T + w
print(f"  a=2 conjugation check: sigma(f1) - f2 = {sp.simplify(sp.expand(f1_a2_conj - f2_a2))}")

# Also confirm L_a2 is genuinely IRREDUCIBLE over Q (the premise)
print(f"  a=2 irreducible over Q?  factor_list: {sp.factor_list(L_a2, T)}")
print(f"  a=3 irreducible over Q?  factor_list: {sp.factor_list(L_a3, T)}")
print()

# ============================================================
# §2.3 IDEA: cubic base-change poly for a=2 equals EXACTLY
#            (13^3 Y^2 + 18 Y + 13^3)^2 / 2197^2
# ============================================================
print("=== §2.3: exact base-change factorization for a=2 ===")

# Build base-changed poly from the ACTUAL Frobenius eigenvalues (roots of L_a2).
# L_a2(T) = prod(1 - alpha_i T). Get alpha_i exactly, cube them, rebuild.
roots_T = sp.solve(L_a2, T)   # these are 1/alpha_i
alphas = [sp.simplify(1/r) for r in roots_T]
print(f"  alphas (Frobenius eigenvalues): {[sp.nsimplify(sp.simplify(a)) for a in alphas]}")

cubed = [sp.expand(a**3) for a in alphas]
# base-changed L^(3)(Y) = prod(1 - alpha_i^3 Y)
Lbc = 1
for c in cubed:
    Lbc = sp.expand(Lbc * (1 - c*Y))
Lbc = sp.simplify(Lbc)
print(f"  L^(3)(Y) rebuilt from cubed roots = {sp.nsimplify(Lbc)}")

# Document's claimed factorization
claim_bc = ((13**3 * Y**2 + 18*Y + 13**3)/2197)**2
claim_bc_exp = sp.expand(claim_bc)
print(f"  Document claims (13^3 Y^2 + 18Y + 13^3)^2 / 2197^2 = {sp.nsimplify(claim_bc_exp)}")

diff_bc = sp.simplify(Lbc - claim_bc_exp)
print(f"  Difference = {diff_bc}   ->  {'EXACT MATCH' if diff_bc==0 else 'MISMATCH'}")

# Also check against the document's explicitly-written expanded coefficients:
# (1/4826809)Y^4 + (36/4826809)Y^3 + (4718/4826809)Y^2 + (36/2197)Y + 1
doc_expanded = (sp.Rational(1,4826809)*Y**4 + sp.Rational(36,4826809)*Y**3
                + sp.Rational(4718,4826809)*Y**2 + sp.Rational(36,2197)*Y + 1)
print(f"  Doc's expanded form matches its own square? {sp.simplify(doc_expanded - claim_bc_exp)==0}")
print(f"  Doc's expanded form matches TRUE base-change? {sp.simplify(doc_expanded - Lbc)==0}")
