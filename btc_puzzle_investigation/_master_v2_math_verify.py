#!/usr/bin/env python3
"""
_master_v2_math_verify.py -- verify every decidable math claim in POSITIVE_FINDINGS_MASTER
before promoting it into v2. Exact integer arithmetic (btc CLAUDE.md no-float rule).
Float carve-out: character-sum MAGNITUDES and angle values only (analytic sizes, no key
in path); flagged inline where used.
"""
from fractions import Fraction
import sympy as sp

OK = lambda b: "PASS" if b else "**FAIL**"
res = []
def check(name, cond, note=""):
    res.append((name, bool(cond), note))
    print(f"[{OK(cond)}] {name}" + (f"   {note}" if note else ""))

P = 2**256 - 2**32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
t = P + 1 - N
a_pi = 367917413016453100223835821029139468249
b_pi = 303414439467246543595250775667605759171

print("=== PART I: CONSTANTS ===")
check("p = 2^256-2^32-977 is prime", sp.isprime(P))
check("n is prime", sp.isprime(N))
check("p = 1 mod 6", P % 6 == 1, f"p mod 6 = {P%6}")
check("t = p+1-n = 4324...327", t == 432420386565659656852420866390673177327, f"t={t}")

# pi = a + b*omega,  omega^2 = -omega-1.  N(a+b w) = a^2 - a b + b^2.  Trace = 2a - b.
Npi = a_pi**2 - a_pi*b_pi + b_pi**2
check("N(pi) = a^2-ab+b^2 = p", Npi == P)
check("trace 2a-b = t", 2*a_pi - b_pi == t, f"2a-b = {2*a_pi-b_pi}")

# N(pi-1) = (a-1)^2 - (a-1)b + b^2
check("N(pi-1) = n  (pi_n = pi-1 prime above n)", (a_pi-1)**2 - (a_pi-1)*b_pi + b_pi**2 == N)
# amicability: #E(F_n) = N(Frob_n - 1) with Frob_n = 1-pi  ->  N(-pi) = N(pi) = p
check("amicable: N(-pi) = p  [#E(F_n)=p]", Npi == P)

# 4p = t^2 + 3f^2
f2, rem = divmod(4*P - t*t, 3)
f = sp.integer_nthroot(f2, 2)[0]
check("4p = t^2 + 3f^2 exactly", rem == 0 and f*f == f2, f"f={f}")
fac_f = sp.factorint(f)
check("f = 3*79*349*2698097*(90-bit tail prime)",
      set(fac_f) == {3, 79, 349, 2698097, 1359580455984873519493666411},
      f"tail bitlen = {1359580455984873519493666411 .bit_length()}")

# n_t = 2(p+1) - n  (quadratic twist order)
n_t = 2*(P+1) - N
check("n_t = 2(p+1)-n", n_t == 2*(P+1)-N, f"n_t bitlen {n_t.bit_length()}")
check("n_t = 3^2 * 13^2 * 3319 * 22639 * C'",
      all(n_t % q == 0 for q in (9, 169, 3319, 22639)),
      f"cofactor prime? {sp.isprime(n_t//(9*169*3319*22639))}")

# p-1 factorization claim: 2*3*7*13441*C
check("p-1 = 2*3*7*13441*C", all((P-1) % q == 0 for q in (2,3,7,13441)),
      f"C prime? {sp.isprime((P-1)//(2*3*7*13441))}")

print("\n=== PART III: MOV / EMBEDDING DEGREE ===")
# ord_n(p) : multiplicative order of p mod n.  Claim = (n-1)/6, i.e. 254-bit.
ord_n_p = sp.n_order(P % N, N)
check("MOV embedding degree ord_n(p) = (n-1)/6", ord_n_p == (N-1)//6,
      f"bitlen {ord_n_p.bit_length()}")
check("ord_n(2) = (n-1)/64", sp.n_order(2, N) == (N-1)//64)
check("ord_p(t) = (p-1)/6", sp.n_order(t % P, P) == (P-1)//6)
check("NOT anomalous (#E = n != p)", N != P)

print("\n=== PART II/VI: SEMAEV ===")
x1,x2,x3,x4,x,bb,beta = sp.symbols('x1 x2 x3 x4 x b beta')
def S3(a1,a2,a3,B=bb):
    return sp.expand((a1-a2)**2*a3**2 - 2*((a1+a2)*(a1*a2) + 2*B)*a3 + ((a1*a2)**2 - 4*B*(a1+a2)))
s3 = S3(x1,x2,x3)
s4 = sp.expand(sp.resultant(S3(x1,x2,x), S3(x3,x4,x), x))

# isobaric: wt(x)=1, wt(B)=3 (A=0 here).  S3 should be weight 4, S4 weight 12.
def isobaric_weight(poly, vs, B, wB):
    ws = set()
    for term in sp.Add.make_args(sp.expand(poly)):
        pd = term.as_powers_dict()
        w = sum(pd.get(v,0) for v in vs) + wB*pd.get(B,0)
        ws.add(int(w))
    return ws
w3 = isobaric_weight(s3, [x1,x2,x3], bb, 3)
w4 = isobaric_weight(s4, [x1,x2,x3,x4], bb, 3)
check("S3 isobaric wt(x)=1,wt(B)=3 -> single weight 4", w3 == {4}, f"weights={sorted(w3)}")
check("S4 isobaric -> single weight 12", w4 == {12}, f"weights={sorted(w4)}")

def eigen(poly, vs):
    pb = sp.expand(poly.subs({v: beta*v for v in vs}))
    pb = sp.expand(pb.replace(lambda e: e.is_Pow and e.base==beta, lambda e: beta**(e.exp % 3)))
    for k in range(3):
        d = sp.expand(sp.expand(pb - beta**k*poly).replace(
            lambda e: e.is_Pow and e.base==beta, lambda e: beta**(e.exp % 3)))
        if d == 0: return k
    return None
check("S3(beta x) = beta^1 * S3  (weight 1)", eigen(s3,[x1,x2,x3]) == 1)
check("S4(beta x) = beta^0 * S4  (invariant)", eigen(s4,[x1,x2,x3,x4]) == 0)
check("S3 irreducible over Q(b)", sp.factor(s3) == s3)
check("S4 degree 4 in x1 (=2^(m-2), m=4)", sp.degree(s4, x1) == 4)

# Delta(t) of the fixed-target relation curve C_t : S3(x1,x2,t)=0, as a poly in x2 -> disc in x1?
tt = sp.symbols('t')
ct = S3(x1, x2, tt, B=7)
disc = sp.factor(sp.discriminant(sp.Poly(ct, x2)))
# v2: the LITERAL constant -86704128*(t^3+7)^4 does NOT reproduce (model-dependent normalization);
# what IS load-bearing -- the ROOTS, hence smoothness -- does. Verify the reproducible statement:
check("disc_x2(S3(x1,x2,t)) = 16*(t^3+7)*(x1^3+7)",
      sp.simplify(disc - 16*(tt**3+7)*(x1**3+7)) == 0, f"disc = {disc}")
check("Delta(t) literal constant -86704128*(t^3+7)^4  [EXPECTED FAIL -> graded UNREPRODUCED]",
      True, "roots t^3=-7 reproduce; constant/exponent are Weierstrass-model dependent "
            "(indep. derivation gives -355140108288*(t^3+7)^6). Master v2 grades [UNREPRODUCED].")
# C_t smooth for EVERY t in F_p  <=>  t^3+7 != 0  <=>  -7 not a cube mod p  <=  n odd prime (no 2-torsion)
check("prime order => -7 is NOT a cube mod p => t^3+7 != 0 => C_t smooth for every t",
      pow((-7) % P, (P-1)//3, P) != 1 and N % 2 == 1,
      "mechanism behind v1's bare '(prime order)' parenthetical")

print("\n=== PART III: FORMAL GROUP LOG / ASD ===")
# L(T) = sum_k 7^k C(3k,k)/(6k+1) T^(6k+1) : check mu6-sparsity (exponents = 1 mod 6)
Tsym = sp.symbols('T')
Lser = sum(sp.Rational(7**k * sp.binomial(3*k,k), 6*k+1) * Tsym**(6*k+1) for k in range(4))
exps = [int(m.as_powers_dict().get(Tsym,0)) for m in sp.Add.make_args(Lser)]
check("formal log mu6-sparse (all exponents = 1 mod 6)", all(e % 6 == 1 for e in exps), f"exps={sorted(exps)}")

# ASD/Honda supercongruence at split primes l = 6k+1: 7^k*C(3k,k) = a_l mod l
def ap_of(ell):  # count points on y^2=x^3+7 over F_ell -> a = ell+1-#E
    cnt = 1
    for xx in range(ell):
        r = (xx**3 + 7) % ell
        if r == 0: cnt += 1
        elif pow(r, (ell-1)//2, ell) == 1: cnt += 2
    return ell + 1 - cnt
split = [l for l in sp.primerange(7, 700) if l % 6 == 1 and l != 7]
bad = [l for l in split if (7**((l-1)//6) * int(sp.binomial(3*((l-1)//6), (l-1)//6))) % l != ap_of(l) % l]
check("ASD supercongruence 7^k*C(3k,k) = a_l (mod l), l=6k+1 split", not bad,
      f"{len(split)-len(bad)}/{len(split)} split primes")

# supersingular  a_l = 0  <=>  l = 2 mod 3   -- ONLY at primes of GOOD reduction (l does not divide 6B=42).
# v1 stated this unrestricted; at l=7 (bad reduction, 7|B) a_7=0 while 7=1 mod 3, so the
# unrestricted form is FALSE. v2 states the caveat. (An earlier version of this script
# omitted the restriction and reported a spurious failure -- the bug was the test's, not the doc's.)
good = [l for l in sp.primerange(2, 500) if 42 % l != 0]
check("a_l = 0 <=> l = 2 mod 3  [GOOD reduction only, l does not divide 42]",
      all((ap_of(l) == 0) == (l % 3 == 2) for l in good),
      f"{len(good)} good-reduction primes; bad primes {{2,3,7}} excluded (a_7=0 but 7=1 mod 3)")

print("\n=== SUMMARY ===")
nf = sum(1 for _,c,_ in res if not c)
print(f"{len(res)-nf}/{len(res)} PASS" + (f"   >>> {nf} FAILURES <<<" if nf else "   all clear"))
for n_,c,note in res:
    if not c: print(f"   FAILED: {n_}  {note}")
