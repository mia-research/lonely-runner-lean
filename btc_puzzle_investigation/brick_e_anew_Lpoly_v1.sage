# F2 design input: A_new(F_{p^2}) order + factorization + the rho-scalar (sqrt(-1)) question.
# Structural only (no c(d)-vs-d statistic). Exact integer arithmetic; field ops via GF(p^k).
# L_C from point counts N_1,N_2,N_3 of C: w^4 = x^3+7, Weil functional equation (6 eigenvalues,
# 3 independent e_1,e_2,e_3 with e_4=p*e_2, e_5=p^2*e_1, e_6=p^3).

p = 43; B = 7

def count_C(k):
    q = p**k
    Fq = GF(q)
    # multiset of 4th powers
    from collections import Counter
    pow4 = Counter()
    for w in Fq:
        pow4[w**4] += 1
    N = 1  # one place at infinity (gcd(4,3)=1 => totally ramified, single place)
    for x in Fq:
        c = Fq(x)**3 + Fq(B)
        N += pow4.get(c, 0)
    return N

N1, N2, N3 = count_C(1), count_C(2), count_C(3)
s1 = p + 1 - N1
s2 = p**2 + 1 - N2
s3 = p**3 + 1 - N3
# Newton -> elementary symmetric of the 6 eigenvalues (only need e1,e2,e3)
e1 = s1
e2 = (e1*s1 - s2)//2
e3 = (e2*s1 - e1*s2 + s3)//3
assert (e1*s1 - s2) % 2 == 0 and (e2*s1 - e1*s2 + s3) % 3 == 0, "Newton nonintegral -> count bug"
e4 = p*e2; e5 = p**2*e1; e6 = p**3
# L_C(T) = 1 - e1 T + e2 T^2 - e3 T^3 + e4 T^4 - e5 T^5 + e6 T^6
def LC(T): return 1 - e1*T + e2*T**2 - e3*T**3 + e4*T**4 - e5*T**5 + e6*T**6

JacFp  = LC(1)          # |Jac(F_p)|
JacFp2 = LC(1)*LC(-1)   # |Jac(F_{p^2})| = prod(1-a_i^2) = LC(1)*LC(-1)

# E: y^2=x^3+7, a_E = 13 at p=43 (|E(F_p)|=31)
aE = p + 1 - 31
LE1 = 1 - aE + p          # |E(F_p)|
LE_1 = 1 + aE + p         # |E(F_{p^2})| factor  (=LE(-1))
EFp2 = LE1 * LE_1

AnewFp  = JacFp // LE1
AnewFp2 = JacFp2 // EFp2   # up to 2-power isogeny kernel

print("N1,N2,N3        =", N1, N2, N3)
print("s1,s2,s3        =", s1, s2, s3)
print("e1,e2,e3        =", e1, e2, e3)
print("|Jac(F_p)|      =", JacFp, "  (expect 58683 = 3*31*631)")
print("|E(F_p)|        =", LE1, "   -> |A_new(F_p)| =", AnewFp, "(expect 1893=3*631)")
print("|Jac(F_p^2)|    =", JacFp2, "= ", factor(JacFp2))
print("|E(F_p^2)|      =", EFp2, "=", factor(EFp2))
print("|A_new(F_p^2)|  =", AnewFp2, "=", factor(AnewFp2))

# rho-scalar question: rho^2=[-1]. On a cyclic subgroup of order M', rho acts as mult-by-r with
# r^2 == -1 (mod M') iff sqrt(-1) exists mod M' iff 4 nmid M' and every odd prime factor is 1 mod 4.
def sqrt_minus1_exists(M):
    Mf = Integer(M)
    if Mf % 4 == 0: return False
    for q_, e_ in factor(Mf):
        if q_ == 2:
            if e_ > 1: return False
            continue
        if q_ % 4 != 1: return False
    return True

print("\n--- rho-scalar (sqrt(-1) mod M) feasibility ---")
for label, M in [("A_new(F_p)=1893", AnewFp), ("A_new(F_p^2)", AnewFp2)]:
    print(f"  sqrt(-1) exists mod {label} ({M}) : {sqrt_minus1_exists(M)}")
# largest divisor M' of |A_new(F_p^2)| admitting sqrt(-1) (candidate rho-stable-scalar modulus)
divs = sorted(Integer(AnewFp2).divisors(), reverse=True)
best = next((D for D in divs if D > 1 and sqrt_minus1_exists(D)), 1)
print("  largest divisor of |A_new(F_p^2)| with sqrt(-1):", best, "=", factor(best) if best>1 else "1")
