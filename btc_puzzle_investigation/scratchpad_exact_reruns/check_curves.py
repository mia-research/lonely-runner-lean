# Exact integer point counts (no float). Verify the small curves in claims 1/5 and 6.
def order(p, a4, a6):
    # y^2 = x^3 + a4 x + a6 over F_p ; count affine + point at infinity
    # quadratic residues
    qr = set((i*i) % p for i in range(p))
    cnt = 1  # infinity
    for x in range(p):
        rhs = (x*x*x + a4*x + a6) % p
        if rhs == 0:
            cnt += 1
        elif rhs in qr:
            cnt += 2
    return cnt

def isprime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True

# Claim 1 & 5: E' : y^2 = x^3 + x + 3 over F_43, expect order 47 (prime), non-CM
n1 = order(43, 1, 3)
print("Claim 1/5  E': y^2=x^3+x+3 / F_43  -> order =", n1, " prime?", isprime(n1), " (claim: 47)")
# discriminant -16(4a^3+27b^2) ; is -(4a^3+27b^2) or disc a perfect square?
a4,a6=1,3
disc = -16*(4*a4**3 + 27*a6**2)
print("   disc = -16(4a^3+27b^2) =", disc)

# Claim 6: E : y^2 = x^3 + 14 over F_19, expect order 13 (prime), j=0 (CM by Z[omega])
n6 = order(19, 0, 14)
print("Claim 6    E : y^2=x^3+14  / F_19  -> order =", n6, " prime?", isprime(n6), " (claim: 13)")

# Claim 6 algebra: quadratic W^2+26W+117
D = 26*26 - 4*117
print("   disc(W^2+26W+117) =", D, "= 16*13 ?", D==16*13, "-> roots -13 +/- 2*sqrt(13), field Q(sqrt13)")
