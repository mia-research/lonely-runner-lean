import sympy as sp

# ---- Doc 1: hypergeometric formal group rigidity ----
# Curve y^2 = x^3 + B. Formal log L(z) = sum_j B^j C(3j,j)/(6j+1) z^{6j+1}
B = 7
p = 43

# (A) Verify the claimed series coefficients 1, 3B, 40B^2, ...
z = sp.symbols('z')
terms = []
for j in range(0,5):
    c = sp.binomial(3*j, j)*B**j / (6*j+1)
    terms.append(c*z**(6*j+1))
L = sum(terms)
print("L(z) series coeffs (c_j of z^{6j+1}) for j=0..4:")
for j in range(5):
    c = sp.binomial(3*j,j)*sp.Integer(B)**j/(6*j+1)
    print(f"  j={j}: coeff={c}   (z^{6*j+1})")
print("  claim: 1, 3B=%d, 40B^2=%d" % (3*B, 40*B*B))

# (B) The endomorphism on the formal param: (x,y)->(beta x, y) gives z=-x/y -> beta z EXACTLY.
# beta^3=1. Check L(beta z) == beta*L(z) as a power series identity.
beta = sp.symbols('beta')
Lbz = sum(sp.binomial(3*j,j)*sp.Integer(B)**j/(6*j+1)*(beta*z)**(6*j+1) for j in range(5))
# reduce beta using beta^3=1 => beta^6=1 on the exponent 6j+1 -> beta^{6j+1}=beta
Lbz_reduced = sum(sp.binomial(3*j,j)*sp.Integer(B)**j/(6*j+1)*beta*z**(6*j+1) for j in range(5))
print("\nL(beta z) - beta*L(z) (using beta^6=1):",
      sp.simplify(Lbz.subs(beta**7,beta).rewrite(sp.Pow) - beta*L) if False else sp.expand(Lbz_reduced - beta*L))
print("  => identity holds because 6j+1 ≡ 1 (mod 6) and beta^6=1  [TRUE, and forced]")

# (C) Reproduce their numeric table at z=p=43, mod p^k, k=1..4
def Lval_mod(zz, mod, jmax=20):
    s = 0
    from math import comb
    for j in range(jmax):
        num = comb(3*j,j)*B**j * pow(zz, 6*j+1)
        den = 6*j+1
        # need num/den mod 'mod'; den may share factors with mod=p^k. Handle via rationals then mod.
        s += sp.Rational(num, den)
    # reduce mod
    val = s
    # take mod of the exact rational (den invertible mod p^k iff gcd(den,p)=1)
    from sympy import Integer
    num_r, den_r = sp.fraction(sp.nsimplify(val))
    return (int(num_r) * pow(int(den_r), -1, mod)) % mod

# Hensel lift beta (cube root of unity, the '6 mod 43' branch) to mod p^k
def hensel_cuberoot(mod):
    # find x with x^3=1 mod p^k, x != 1, lifting 6 mod 43
    base = 6
    for cand in range(mod):
        if cand % p == base % p and pow(cand,3,mod)==1:
            return cand
    return None

print("\nNumeric table (z=43):")
for k in range(1,5):
    mod = p**k
    b = hensel_cuberoot(mod)
    Lz  = Lval_mod(43, mod)
    zphi= (b*43) % mod
    Lzphi = Lval_mod(zphi, mod)
    expect = (b*Lz) % mod
    print(f"  k={k} mod {mod}: beta={b}  beta^3 mod={pow(b,3,mod)}  L(z)={Lz}  z_phi={zphi}  L(z_phi)={Lzphi}  beta*L(z)={expect}  diff={(Lzphi-expect)%mod}")
    # ALSO: is L(z) just == z at this precision?
    print(f"       [check] L(z) == z (=43)? {Lz==43%mod}   -> higher terms vanish because v(z^7)=7>k")
