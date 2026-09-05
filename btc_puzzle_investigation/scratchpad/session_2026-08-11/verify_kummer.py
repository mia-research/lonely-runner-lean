import sympy as sp

# ============================================================
# PART A: the document's MODEL set {alpha, alphabar, z*alpha, z^2*alphabar}
#         treat alpha=A, alphabar=B as independent, A*B=p, z=primitive cube root.
# ============================================================
A, B, p, z = sp.symbols('A B p z')
# z^2+z+1=0, z^3=1
def redz(expr):
    expr = sp.expand(expr)
    # replace z^k using z^3=1 then z^2=-z-1
    poly = sp.Poly(expr, z)
    # reduce mod z^2+z+1
    q, r = sp.div(poly, sp.Poly(z**2+z+1, z), z)
    return r.as_expr()

roots = [A, B, z*A, z**2*B]
# elementary symmetric
e1 = sum(roots)
e2 = sum(roots[i]*roots[j] for i in range(4) for j in range(i+1,4))
e3 = sum(roots[i]*roots[j]*roots[k] for i in range(4) for j in range(i+1,4) for k in range(j+1,4))
e4 = roots[0]*roots[1]*roots[2]*roots[3]

# substitute A*B = p everywhere by reducing, then apply z-reduction
def simp(expr):
    expr = sp.expand(expr)
    expr = expr.subs(A*B, p)          # first-order
    # handle higher A*B powers
    expr = sp.expand(expr)
    for k in range(4,0,-1):
        expr = expr.subs(A**k*B**k, p**k)
    expr = redz(expr)
    expr = sp.expand(expr.subs(A*B,p))
    return sp.simplify(expr)

E1=simp(e1); E2=simp(e2); E3=simp(e3); E4=simp(e4)
print("PART A: document's model set {A, B, zA, z^2 B}, A*B=p")
print("  e1 =", E1)
print("  e2 =", E2)
print("  e3 =", E3)
print("  e4 =", E4)

# Document claims: e2 = e1^2 - p, e3 = p*e1, e4 = p^2
check_e2_minus = simp(E2 - (E1**2 - p))
check_e2_plus  = simp(E2 - (E1**2 + p))
check_e3 = simp(E3 - p*E1)
check_e4 = simp(E4 - p**2)
print(f"\n  Doc claim e2 = e1^2 - p ?  residual = {check_e2_minus}  -> {'HOLDS' if check_e2_minus==0 else 'FAILS'}")
print(f"  Alt      e2 = e1^2 + p ?  residual = {check_e2_plus}  -> {'HOLDS' if check_e2_plus==0 else 'FAILS'}")
print(f"  Doc claim e3 = p*e1    ?  residual = {check_e3}  -> {'HOLDS' if check_e3==0 else 'FAILS'}")
print(f"  Doc claim e4 = p^2     ?  residual = {check_e4}  -> {'HOLDS' if check_e4==0 else 'FAILS'}")

# ============================================================
# PART B: do the REAL A_new eigenvalues match this model + these identities?
#   non-residue: sqrt(p) * roots of x^4+x^2+1  = sqrt(p){z6, z6^5, z3, z3^2}
#   residue    : {sqrt(p), sqrt(p), -sqrt(p), -sqrt(p)}  (char poly (X^2-p)^2)
# ============================================================
print("\n" + "="*60)
print("PART B: REAL A_new eigenvalues vs the model / identities")
print("="*60)
import cmath, math
for pval in [43, 67]:
    sp_ = math.sqrt(pval)
    z6 = cmath.exp(1j*math.pi/3)
    z3 = cmath.exp(2j*math.pi/3)
    real_nonres = [sp_*z6, sp_*z6**5, sp_*z3, sp_*z3**2]
    real_res    = [sp_, sp_, -sp_, -sp_]
    for name, ev in [("non-residue", real_nonres), ("residue", real_res)]:
        s1 = sum(ev)
        s2 = sum(ev[i]*ev[j] for i in range(4) for j in range(i+1,4))
        s3 = sum(ev[i]*ev[j]*ev[k] for i in range(4) for j in range(i+1,4) for k in range(j+1,4))
        s4 = ev[0]*ev[1]*ev[2]*ev[3]
        e1r=round(s1.real,4); e2r=round(s2.real,4); e3r=round(s3.real,4); e4r=round(s4.real,4)
        print(f"\n  p={pval} {name}: e1={e1r} e2={e2r} e3={e3r} e4={e4r}")
        print(f"    e1^2 - p = {round((s1**2).real - pval,4)}   e1^2 + p = {round((s1**2).real + pval,4)}   (actual e2={e2r})")
        # does e2 = e1^2 - p hold for the REAL values?
        holds_minus = abs(s2 - (s1**2 - pval)) < 1e-6
        holds_plus  = abs(s2 - (s1**2 + pval)) < 1e-6
        print(f"    real e2 = e1^2 - p (doc's identity)? {holds_minus}    e2 = e1^2 + p? {holds_plus}")

        # Can the real spectrum be written as {a, abar, z3*a, z3^2*abar}? i.e. is there
        # a pairing where one pair is z3 times the (conjugate-flipped) other?
        # Test: does there exist a in ev with z3*a also in ev (up to matching)?
        def near(x, lst):
            return any(abs(x-y)<1e-6 for y in lst)
        z3c = z3
        pairs_z3 = sum(1 for a_ in ev if near(z3c*a_, ev))
        print(f"    #eigenvalues a with z3*a also an eigenvalue (doc's phase-lock a3=z3*a1): {pairs_z3}/4")
