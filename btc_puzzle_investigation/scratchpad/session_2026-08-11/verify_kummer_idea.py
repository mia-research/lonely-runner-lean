import sympy as sp

# Test the IDEA (not the doc's coordinates): does the REAL A_new spectrum decompose
# as  H^1_new = W (+) W(x)zeta3,  i.e. spectrum = S  U  zeta3*S  for some 2-set S,
# and does complex conjugation swap the two halves?  For BOTH branches (res / non-res).
# Work with normalized eigenvalues u = alpha/sqrt(p) (exact roots of unity).

z3 = sp.exp(2*sp.pi*sp.I/3)         # primitive cube root
z6 = sp.exp(sp.pi*sp.I/3)           # primitive 6th root

def eq(a,b): return sp.simplify(a-b)==0
def inset(x, S): return any(eq(x,s) for s in S)

def test_branch(name, U):
    print(f"\n--- {name} branch: normalized eigenvalues u = {[sp.nsimplify(v) for v in U]} ---")
    # e1,e2 of the normalized set (should be 0, +1 for nonres; 0,-2 for res -> times p gives the real)
    e1 = sum(U); e2 = sum(U[i]*U[j] for i in range(4) for j in range(i+1,4))
    print(f"    e1={sp.simplify(e1)}  e2={sp.simplify(e2)}   (times p: real e2 = {sp.simplify(e2)}*p)")

    # (1) twist test: is U = S u z3*S for some 2-subset S?
    from itertools import combinations
    found_S=None
    for S in combinations(range(4),2):
        Sset=[U[i] for i in S]
        rest=[U[i] for i in range(4) if i not in S]
        twist=[sp.simplify(z3*s) for s in Sset]
        # does {twist} == {rest} as multisets?
        used=[False]*2; ok=True
        for t in twist:
            m=-1
            for j in range(2):
                if not used[j] and eq(t,rest[j]): m=j; break
            if m<0: ok=False; break
            used[m]=True
        if ok:
            found_S=Sset; break
    print(f"    spectrum = S u zeta3*S (twist decomposition)?  {'YES, S='+str([sp.nsimplify(s) for s in found_S]) if found_S else 'NO'}")

    # (2) conjugation-swap test: does conj(S) == zeta3*S (the other half)?
    if found_S:
        Sset=found_S
        conjS=[sp.simplify(sp.conjugate(s)) for s in Sset]
        twistS=[sp.simplify(z3*s) for s in Sset]
        # conj(S) should equal the OTHER half = twistS (as sets)
        used=[False]*2; swap=True
        for c in conjS:
            m=-1
            for j in range(2):
                if not used[j] and eq(c,twistS[j]): m=j;break
            if m<0: swap=False;break
            used[m]=True
        print(f"    complex conjugation swaps W <-> W(x)z3 (doc §4)?  {swap}")

    # (3) the doc's specific model {a, abar, z3 a, z3^2 abar} with abar=conj(a): can it
    #     reproduce this set for any a?  (its distinctive claim / where e2=e1^2-p came from)
    reproducible=False
    for i in range(4):
        a=U[i]; abar=sp.simplify(sp.conjugate(a))
        model=[a, abar, sp.simplify(z3*a), sp.simplify(z3**2*abar)]
        # compare as sets to U
        used=[False]*4; ok=True
        for m in model:
            k=-1
            for j in range(4):
                if not used[j] and eq(m,U[j]): k=j;break
            if k<0: ok=False;break
            used[k]=True
        # also require model has 4 DISTINCT elements (non-degenerate)
        distinct=all(not eq(model[x],model[y]) for x in range(4) for y in range(x+1,4))
        if ok and distinct: reproducible=True; break
    print(f"    doc's {{a,abar,z3 a,z3^2 abar}} reproduces this set (non-degenerately)?  {reproducible}")

# non-residue: roots of x^4+x^2+1 = primitive 3rd/6th roots
U_nonres=[z6, z6**5, z3, z3**2]
# residue: (x^2-1)^2 -> {1,1,-1,-1}
U_res=[sp.Integer(1), sp.Integer(1), sp.Integer(-1), sp.Integer(-1)]

test_branch("NON-RESIDUE (c2=+p)", U_nonres)
test_branch("RESIDUE (c2=-2p)", U_res)

print("\n\n=== SUMMARY ===")
print("The IDEA = twist decomposition H^1_new = W (+) W(x)zeta3 with conjugation swap.")
print("Tested against the REAL supersingular spectrum, both branches.")
