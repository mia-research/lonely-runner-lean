#!/usr/bin/env python3
"""
test_anew_identification_v1.py  --  2026-07-30

Closes the residual named in RESULT_star_adversarial_review_v1.md §2:
tie the chi_4-ISOTYPIC factor of Jac(C), C : w^4 = f(x), to "the NEW PART complementary
to E" -- the project's definition of A_new (RESULT_mu4_eigenvalue_individual_v1.md:6).

The identification argument (2 lines, verified numerically below):
  * The subgroup <-1> of mu_4 acts by w -> -w.  The quotient C/<-1> is  y^2 = f(x) = E,
    via y = w^2.  Pullback embeds Jac(E) into Jac(C) with image the <-1>-INVARIANT part,
    i.e. the j even eigenspaces (j=0 contributes 0, so: the j=2 part).
  * Hence the complement -- "the new part" -- is the sum of the eigenspaces on which -1
    acts by -1, i.e. j odd, i.e. j in {1,3}.  And j in {1,3} are exactly the FAITHFUL
    characters of mu_4, i.e. the chi_4-isotypic part (chi_4 and its conjugate).
  => new part complementary to E  ==  chi_4-isotypic factor.   QED

Numerical confirmation of both consequences, exact integers only:
  (T1)  #C(F_p)    = p  + 1 - a_p                      <=>  b_1(A_new) = 0
  (T2)  #C(F_p^2)  = p^2 + 1 - a_p^2 + 2p + 2*S        <=>  b_2(A_new) = S
  (T3)  m = S/p is an integer in {-2,1,2} and matches the A2.1 cubic-residue branch.

NO FLOATING POINT.  F_{p^2} = F_p[t]/(t^2+1) (valid for p = 3 mod 4) as integer pairs.
chi_4(x) = x^((q-1)/4) evaluated IN the field, landing in mu_4 = {1,-1,t,-t}; recorded as
an exponent in Z/4 and summed as an element of Z[i].  No discrete log, no float.
"""

# ---------- exact F_{p^2} = F_p[t]/(t^2+1) ----------
def mul(a, b, p):
    (x0, x1), (y0, y1) = a, b
    return ((x0 * y0 - x1 * y1) % p, (x0 * y1 + x1 * y0) % p)


def powf(a, e, p):
    r = (1, 0)
    while e:
        if e & 1:
            r = mul(r, a, p)
        a = mul(a, a, p)
        e >>= 1
    return r


def elements(p):
    return [(u, v) for u in range(p) for v in range(p)]


# ---------- exact point counts ----------
def count_C_Fp(p, B):
    """#C(F_p) for C : w^4 = x^3 + B, smooth model. gcd(4,3)=1 => ONE point at infinity."""
    quart = [0] * p
    for w in range(p):
        quart[(w * w % p) * (w * w % p) % p] += 1
    return sum(quart[(x * x % p * x + B) % p] for x in range(p)) + 1


def count_C_Fp2(p, B):
    els = elements(p)
    quart = {}
    for w in els:
        u = mul(mul(w, w, p), mul(w, w, p), p)
        quart[u] = quart.get(u, 0) + 1
    tot = 0
    Bf = (B % p, 0)
    for x in els:
        u = mul(mul(x, x, p), x, p)
        u = ((u[0] + Bf[0]) % p, (u[1] + Bf[1]) % p)
        tot += quart.get(u, 0)
    return tot + 1


def legendre(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p - 1) // 2, p) == 1 else -1)


def a_p_of_E(p, B):
    """trace of Frobenius for E : y^2 = x^3 + B over F_p, exact."""
    n = p + 1 + sum(legendre((x * x % p * x + B) % p, p) for x in range(p))
    return p + 1 - n


def S_exact(p, B):
    """S = sum_{x in F_{p^2}} chi_4(x^3 + B), exact, as (re, im) in Z[i]."""
    q = p * p
    e = (q - 1) // 4
    # mu_4 in F_{p^2}: 1, -1, t, -t  ->  exponents 0,2,1,3  (t <-> complex i)
    mu = {(1, 0): 0, (p - 1, 0): 2, (0, 1): 1, (0, p - 1): 3}
    cnt = [0, 0, 0, 0]
    Bf = (B % p, 0)
    for x in elements(p):
        u = mul(mul(x, x, p), x, p)
        u = ((u[0] + Bf[0]) % p, (u[1] + Bf[1]) % p)
        if u == (0, 0):
            continue                      # chi_4(0) = 0
        v = powf(u, e, p)
        cnt[mu[v]] += 1
    re = cnt[0] - cnt[2]
    im = cnt[1] - cnt[3]
    return re, im


print("=" * 96)
print("A_new identification: numerical confirmation of b_1 = 0 and b_2 = S")
print("C : w^4 = x^3 + B   (genus 3)   Jac(C) ~ E x A_new,  dim A_new = 2")
print("=" * 96)
print(f"{'p':>4} {'B':>3} {'p%12':>5} {'cubic res':>10} {'S':>8} {'Im S':>5} "
      f"{'m=S/p':>6} {'T1 b1=0':>8} {'T2 b2=S':>8} {'T3 branch':>10}")
print("-" * 96)

ok = {"T1": [0, 0], "T2": [0, 0], "T3": [0, 0]}
for p in [7, 11, 19, 23, 31, 43, 47, 59]:
    for B in [7, 2, 11, 1, 3]:
        if B % p == 0:
            continue
        ap = a_p_of_E(p, B)
        re, im = S_exact(p, B)
        cC1, cC2 = count_C_Fp(p, B), count_C_Fp2(p, B)

        t1 = (cC1 == p + 1 - ap)                                  # b_1 = 0
        t2 = (cC2 == p * p + 1 - ap * ap + 2 * p + 2 * re)        # b_2 = S
        m_ok = (re % p == 0)
        m = re // p if m_ok else None

        # A2.1 branch prediction
        if p % 12 == 11:
            pred = 2
        else:
            pred = -2 if pow(B, (p - 1) // 3, p) == 1 else 1
        t3 = m_ok and (m == pred) and (im == 0)

        for k, v in (("T1", t1), ("T2", t2), ("T3", t3)):
            ok[k][0 if v else 1] += 1
        cr = "-" if p % 12 == 11 else ("yes" if pow(B, (p - 1) // 3, p) == 1 else "no")
        print(f"{p:>4} {B:>3} {p%12:>5} {cr:>10} {re:>8} {im:>5} "
              f"{str(m):>6} {'PASS' if t1 else 'FAIL':>8} {'PASS' if t2 else 'FAIL':>8} "
              f"{('PASS ' + str(pred)) if t3 else 'FAIL':>10}")

print("-" * 96)
for k in ("T1", "T2", "T3"):
    print(f"  {k}: {ok[k][0]} pass / {ok[k][1]} fail")
print()
print("T1 tests b_1(A_new) = 0 directly:  #C(F_p) = p+1-a_p holds iff the j=1,3 blocks")
print("   contribute zero trace over F_p -- which is Frob swapping them (p = 3 mod 4).")
print("T2 tests b_2(A_new) = S:  Sum(beta^2) = b_1^2 - 2*b_2 = -2*S when b_1 = 0.")
print("T3 tests the composite claim m = S/p integral AND equal to the A2.1 branch.")
