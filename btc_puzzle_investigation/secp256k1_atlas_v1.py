"""secp256k1 feature atlas — exploration v1.
Map EXACT algebraic/dynamical features of y^2 = x^3 + 7 over F_p (a=0,b=7).
Not statistics (those are Weil-bounded); this is the curve's arithmetic structure.
All exact integers. Polynomial root-counting via gcd(x^p - x, f) over F_p."""
p  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
b  = 7

def leg(a, m):
    a %= m
    return 0 if a == 0 else (1 if pow(a, (m-1)//2, m) == 1 else -1)
def is_cube(a):                       # p ≡ 1 mod 3
    a %= p
    return a == 0 or pow(a, (p-1)//3, p) == 1
def sqrt_p(a):                        # p ≡ 3 mod 4
    r = pow(a % p, (p+1)//4, p)
    return r if (r*r) % p == a % p else None

# ---- polynomials over F_p as coeff lists (low->high) ----
def pnorm(f):
    while len(f) > 1 and f[-1] % p == 0: f.pop()
    return [c % p for c in f]
def pmul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b): r[i+j] = (r[i+j] + ai*bj) % p
    return pnorm(r)
def pmod(a, m):
    a = pnorm(a[:]); m = pnorm(m[:]); dm = len(m)-1; inv = pow(m[-1], -1, p)
    while len(a)-1 >= dm and a != [0]:
        c = (a[-1]*inv) % p; sh = len(a)-1-dm
        for i in range(len(m)): a[sh+i] = (a[sh+i] - c*m[i]) % p
        a = pnorm(a)
    return a
def ppowmod(base, e, m):              # base^e mod m  in F_p[x]/m
    r = [1]; base = pmod(base, m)
    while e:
        if e & 1: r = pmod(pmul(r, base), m)
        base = pmod(pmul(base, base), m); e >>= 1
    return r
def pgcd(a, b):
    a = pnorm(a[:]); b = pnorm(b[:])
    while b != [0] and not (len(b) == 1 and b[0] == 0):
        a, b = b, pmod(a, b)
        if len(b) == 1 and b[0] == 0: break
    inv = pow(a[-1], -1, p); return pnorm([c*inv for c in a])
def num_roots_Fp(f):                  # # distinct roots of f in F_p
    f = pnorm(f[:])
    xp = ppowmod([0, 1], p, f)        # x^p mod f
    xpx = pnorm([(xp[i] if i < len(xp) else 0) - (1 if i == 1 else 0) for i in range(max(len(xp), 2))])
    g = pgcd(f, xpx)
    return len(g) - 1

print("="*66)
print("secp256k1 atlas v1 —  y² = x³ + 7  over F_p")
print("="*66)
print(f"\n[A] arithmetic type")
print(f"  p mod 4 = {p%4}  (=3 ⇒ sqrt = a^((p+1)/4))")
print(f"  p mod 3 = {p%3}  n mod 3 = {n%3}  (=1 ⇒ cube roots exist; GLV)")
print(f"  p mod 8 = {p%8}   n mod 4 = {n%4}")
print(f"  (p-1)/2 factors of 2: {((p-1)&-(p-1)).bit_length()-1};  (n-1) 2-adic val: {((n-1)&-(n-1)).bit_length()-1}")

print(f"\n[B] special points over F_p (exact loci)")
# 2-torsion: x^3+7=0  (points (x,0)); exists iff -7 is a cube
r2 = num_roots_Fp([b, 0, 0, 1])       # x^3 + 7
print(f"  2-torsion  x³+7=0 : {r2} root(s)  (0 ⇒ #E odd, no 2-torsion; -7 is a non-cube: {not is_cube(-7)})")
# x=0 point
print(f"  x=0 point (0,√7)  : 7 is QR? {leg(b,p)==1}  ⇒ {'(0,±√7) ∈ E(F_p)' if leg(b,p)==1 else '(0,√7) ∈ E(F_p²) only'}")
# x=y locus: x²=x³+7 → x³-x²+7=0
print(f"  x=y  points x³−x²+7=0 : {num_roots_Fp([b,0,-1,1])} F_p-root(s)")
# x=-y locus: same x condition (y²=x²)
print(f"  x=−y points (same x²=x³+7) share the above locus")
# points with x a perfect ... skip

print(f"\n[C] 3-torsion (fixed pts of x-doubling map): ψ₃ = 3x⁴+12b·x = 3x(x³+28)")
# ψ_3 for a=0: 3x^4 + 6a x^2 + 12b x - a^2 = 3x^4 + 84x
print(f"  x=0 is a root; other roots x³=−28.  −28 a cube mod p? {is_cube(-28)}")
r3 = num_roots_Fp([0, 12*b % p, 0, 0, 3])
print(f"  ψ₃ has {r3} F_p-root(s) ⇒ that many 3-torsion x-coords are F_p-rational")
print(f"  (n mod 3 = {n%3} ≠ 0 ⇒ E(F_p) has NO order-3 point; 3-torsion lives in an extension)")

print(f"\n[D] embedding-degree tower: ord_ℓ(p) = k ⇒ μ_ℓ and pairings live in F_{{p^k}}")
def order_mod(a, l):
    if a % l == 0: return None
    o = 1; x = a % l
    while x != 1: x = (x*a) % l; o += 1
    return o
print("   ℓ  : ord_ℓ(p)   ℓ|n?   ℓ|(p−1)?")
for l in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]:
    print(f"  {l:3d} : {str(order_mod(p,l)):>6}      {'yes' if n%l==0 else 'no ':>3}    {'yes' if (p-1)%l==0 else 'no'}")

print(f"\n[E] automorphism group (order 6: ±1, ±[β], ±[β²])")
beta = pow(3, (p-1)//3, p)
lam  = pow(2, (n-1)//3, n)
print(f"  β³ mod p = {pow(beta,3,p)} (=1)   λ²+λ+1 mod n = {(lam*lam+lam+1)%n} (=0)")
print(f"  β-triple of Gx: {{{hex(Gx)[:10]}.., {hex(beta*Gx%p)[:10]}.., {hex(beta*beta*Gx%p)[:10]}..}} (3 distinct x on the λ-orbit)")
print(f"  distinct? {len({Gx, beta*Gx%p, beta*beta*Gx%p})==3}")
