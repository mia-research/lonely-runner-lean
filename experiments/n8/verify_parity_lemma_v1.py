"""Task 1: exhaustive re-derivation of the Parity Lemma at n=8.
No decimals anywhere; pure integer arithmetic in Z/8."""
n = 8

def Sol(e, j, n):
    return frozenset(r for r in range(n) if (e*r - j) % n == 0)

def bad(e, t, n):
    return Sol(e, (-t) % n, n) | Sol(e, (-(t+1)) % n, n)

units = [e for e in range(1, n) if __import__('math').gcd(e, n) == 1]
nonunits = [e for e in range(1, n) if __import__('math').gcd(e, n) != 1]
print("units mod 8:", units, " non-units in {1..7}:", nonunits)

# (a) every unit is its own inverse
print("\n[a] self-inverse check:", {e: (e*e) % n for e in units},
      "ALL==1:", all((e*e) % n == 1 for e in units))

# (b) for units: bad = {-t e, -(t+1) e}, size 2, one odd one even
ok_b = True
for e in units:
    for t in range(0, 64):          # t is any integer floor state; period 8 in t
        B = bad(e, t, n)
        claimed = frozenset({(-t*e) % n, (-(t+1)*e) % n})
        par = sorted({x % 2 for x in B})
        if B != claimed or len(B) != 2 or par != [0, 1]:
            ok_b = False
            print("  FAIL", e, t, sorted(B), sorted(claimed), par)
print("[b] units: bad=={-te,-(t+1)e}, |bad|==2, exactly one odd+one even, all t in 0..63:", ok_b)

# (c) non-units: bad is a single coset of H_g (or empty), inside ONE parity class
H = {g: frozenset(r for r in range(n) if (r * (n//g)) % n == r and True) for g in ()}  # placeholder
def Hsub(e):
    return frozenset(r for r in range(n) if (e*r) % n == 0)   # kernel of mult-by-e
ok_c = True
for e in nonunits:
    g = __import__('math').gcd(e, n)
    K = Hsub(e)
    print(f"  e={e}: g=gcd(e,8)={g}, kernel H={sorted(K)}, |H|={len(K)}, all even: {all(x%2==0 for x in K)}")
    for t in range(0, 64):
        B = bad(e, t, n)
        S1, S2 = Sol(e, (-t) % n, n), Sol(e, (-(t+1)) % n, n)
        # exactly one of S1,S2 nonempty?
        nonempty = [S for S in (S1, S2) if S]
        is_coset = (len(nonempty) <= 1)
        one_parity = (len({x % 2 for x in B}) <= 1)
        if not (is_coset and one_parity):
            ok_c = False
            print("  FAIL", e, t, sorted(B), sorted(S1), sorted(S2))
print("[c] non-units: >=1 of the two Sol sets empty (so bad is ONE coset) AND bad lies in one parity class:", ok_c)

# (d) the operative consequence: a non-unit can never block both an odd and an even residue
ok_d = all(len({x % 2 for x in bad(e, t, n)}) <= 1 for e in nonunits for t in range(64))
print("[d] no non-unit e in {2,4,6} blocks both parities, any t:", ok_d)

# (e) sizes actually attained
for e in nonunits:
    sizes = sorted({len(bad(e, t, n)) for t in range(8)})
    print(f"  e={e}: attained |bad| values over t mod 8: {sizes}")
