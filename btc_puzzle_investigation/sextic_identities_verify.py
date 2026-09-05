"""Verify four CM/sextic structural identities for secp256k1, exact integer arithmetic.
ZZ[omega]: element (a,b) = a + b*omega, omega^2 = -1-omega. N(a+b w)=a^2-ab+b^2."""
import math
from sympy import factorint, isprime

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
t = p + 1 - n

# ---- Frobenius pi = a + b*omega, N(pi)=p, pi+conj(pi)=2a-b=t ----
D = 4*p - t*t
assert D % 3 == 0
f = math.isqrt(D // 3); assert 3*f*f == D
a = (t + f) // 2; b = f
def norm(z): return z[0]*z[0] - z[0]*z[1] + z[1]*z[1]
def mul(x, y):
    (a,b),(c,d) = x,y
    return (a*c - b*d, a*d + b*c - b*d)
def conj(z): return (z[0]-z[1], -z[1])
pi = (a, b)
assert norm(pi) == p and 2*a - b == t
print(f"pi = {a} + {b}*omega,  N(pi)=p OK,  pi+conj = 2a-b = t OK")

units = {'1':(1,0), '-1':(-1,0), 'w':(0,1), '-w':(0,-1), 'w^2':(-1,-1), '-w^2':(1,1)}

# ===== Claim 1: N(pi+u)=n has the unique solution u=-1, set by sextic class of 7 =====
print("\n=== Claim 1: which unit u gives N(pi+u)=n ? ===")
for name,u in units.items():
    z = (pi[0]+u[0], pi[1]+u[1]); nz = norm(z)
    tag = " <-- = n" if nz==n else (" (=p+t+1)" if nz==p+t+1 else "")
    print(f"  u={name:4s}: N(pi+u) = {'n' if nz==n else ('p+t+1' if nz==p+t+1 else str(nz)[:20]+'...')}{tag}")
# sextic residue class of 7 mod pi (the CM normalization that fixes the twist / the unit)
w = (-a * pow(b, -1, p)) % p            # image of omega in ZZ[w]/pi = F_p  (a+b*w=0 mod p)
assert (w*w + w + 1) % p == 0
def sextic_symbol(lam, pi_ab, modulus):
    """[lam/pi]_6 as exponent k in basis zeta6 = -w^2, over F_modulus."""
    aa,bb = pi_ab
    wm = (-aa * pow(bb, -1, modulus)) % modulus
    assert (wm*wm + wm + 1) % modulus == 0
    val = (lam[0] + lam[1]*wm) % modulus
    s = pow(val, (modulus-1)//6, modulus)
    zeta6 = (-(wm*wm)) % modulus            # primitive 6th root; zeta6^2 = w = omega
    cur = 1
    for k in range(6):
        if cur == s: return k
        cur = (cur*zeta6) % modulus
    return None
k7 = sextic_symbol((7,0), pi, p)
print(f"  sextic residue class [7/pi]_6 = zeta6^{k7}  (zeta6=-w^2, so w=omega=zeta6^2)  -> fixes u")

# ===== Claim 2: pi_n = -(1-pi) = pi-1, a prime above n =====
print("\n=== Claim 2: Grossencharacter relation pi_n = -(1-pi) = pi-1 ===")
pi_n = (pi[0]-1, pi[1])
print(f"  pi_n = pi-1 = {pi_n[0]} + {pi_n[1]}*omega")
print(f"  N(pi_n) = n ? {norm(pi_n)==n};   n mod 3 = {n%3} (=1 => n splits, pi_n is a prime above n)")
print(f"  -(1-pi) = pi-1 identity: {(-(1-pi[0]), -(-pi[1])) == pi_n}")

# ===== Claim 3: sextic reciprocity product = omega (prevents amicability) =====
print("\n=== Claim 3: sextic reciprocity product [pi_n/pi_p]_6 * [pi_p/pi_n]_6 ===")
k_np = sextic_symbol(pi_n, pi,   p)     # [pi_n / pi_p]_6  over F_p
k_pn = sextic_symbol(pi,   pi_n, n)     # [pi_p / pi_n]_6  over F_n
prod = (k_np + k_pn) % 6
label = {0:'1',1:'zeta6',2:'omega (=w^2? ) ',3:'-1',4:'omega^2',5:'-zeta6'}
print(f"  [pi_n/pi_p]_6 = zeta6^{k_np},  [pi_p/pi_n]_6 = zeta6^{k_pn}")
print(f"  product = zeta6^{prod}   (zeta6^2 = omega, zeta6^4 = omega^2, zeta6^3 = -1)")
print(f"  == omega ? {prod==2};  == omega^2 ? {prod==4};  nontrivial (blocks amicability) ? {prod!=0}")

# ===== Claim 4: twist order n_t = 2(p+1)-n, factor, 13^2 -> subgroup of order 169 =====
print("\n=== Claim 4: twist order n_t = 2(p+1)-n and its 169 subgroup ===")
n_t = 2*(p+1) - n
print(f"  n_t = {n_t}")
for q in [3, 9, 13, 169, 3319, 22639]:
    print(f"    {q:6d} | n_t ? {n_t % q == 0}")
cof = n_t // (9 * 169 * 3319 * 22639)
print(f"  n_t / (3^2 * 13^2 * 3319 * 22639) = {cof}")
print(f"    exact division ? {9*169*3319*22639*cof == n_t};  cofactor prime ? {isprime(cof)}")
print(f"  => twist has a rational subgroup of order 169 (from 13^2): {n_t % 169 == 0}")
