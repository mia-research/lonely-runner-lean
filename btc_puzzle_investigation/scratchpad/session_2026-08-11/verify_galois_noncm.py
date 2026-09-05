import itertools, math
from fractions import Fraction

# Reuse field arithmetic from big_sweep
def find_irreducible(p, deg):
    if deg == 2:
        for s in range(1, p):
            if pow(s, (p-1)//2, p) != 1:
                return ('shift', s)
    if deg == 3:
        if (p-1) % 3 == 0:
            for s in range(1, p):
                if not any(pow(x,3,p)==s for x in range(p)):
                    return ('shift', s)
        for c1 in range(0, p):
            for c0 in range(1, p):
                if not any((pow(x,3,p) + c1*x + c0) % p == 0 for x in range(p)):
                    return ('trinomial', c1, c0)
    raise RuntimeError

class FF:
    def __init__(self,p,deg,reduce_map):
        self.p=p; self.deg=deg; self.reduce_map=reduce_map
    def one(self):
        e=[0]*self.deg; e[0]=1; return tuple(e)
    def from_int(self,a):
        e=[0]*self.deg; e[0]=a%self.p; return tuple(e)
    def add(self,a,b): return tuple((x+y)%self.p for x,y in zip(a,b))
    def mul(self,a,b):
        p=self.p; deg=self.deg
        res=[0]*(2*deg-1)
        for i,ai in enumerate(a):
            if ai==0: continue
            for j,bj in enumerate(b):
                if bj==0: continue
                res[i+j]=(res[i+j]+ai*bj)%p
        out=list(res[:deg])
        for k in range(len(res)-1, deg-1, -1):
            c = res[k]
            if c:
                shift = k - deg
                for idx, rc in enumerate(self.reduce_map):
                    tgt = idx + shift
                    if tgt < deg:
                        out[tgt] = (out[tgt] + c*rc) % p
                    else:
                        res[tgt] = (res[tgt] + c*rc) % p
        return tuple(out)
    def pw(self,a,k):
        r=self.one(); b=a
        while k>0:
            if k&1: r=self.mul(r,b)
            b=self.mul(b,b); k>>=1
        return r
    def is_zero(self,a): return all(c==0 for c in a)
    def elements(self):
        for tup in itertools.product(range(self.p),repeat=self.deg): yield tup

class F1:
    def __init__(self,p): self.p_=p
    def one(self): return (1,)
    def from_int(self,a): return (a%self.p_,)
    def add(self,a,b): return ((a[0]+b[0])%self.p_,)
    def mul(self,a,b): return ((a[0]*b[0])%self.p_,)
    def pw(self,a,k): return (pow(a[0],k,self.p_),)
    def is_zero(self,a): return a[0]%self.p_==0
    def elements(self):
        for x in range(self.p_): yield (x,)

def make_field(p, deg):
    if deg == 1:
        return F1(p)
    spec = find_irreducible(p, deg)
    if spec[0] == 'shift':
        s = spec[1]
        reduce_map = [s] + [0]*(deg-1)
    else:
        _, c1, c0 = spec
        reduce_map = [(-c0) % p, (-c1) % p, 0]
    return FF(p, deg, reduce_map)

def count_points(field, N, lin_coef, const_val, quartic):
    g = 4 if quartic else 2
    gg = math.gcd(g, N)
    exp = N // gg
    a_ff = field.from_int(lin_coef)
    b_ff = field.from_int(const_val)
    cnt = 1  # point at infinity
    for x in field.elements():
        x3 = field.mul(field.mul(x, x), x)
        lin = field.mul(a_ff, x) if lin_coef != 0 else field.from_int(0)
        rhs = field.add(field.add(x3, lin), b_ff)
        if field.is_zero(rhs):
            cnt += 1
            continue
        v = field.pw(rhs, exp)
        if v == field.one():
            cnt += gg
    return cnt

def compute_Lnew_coeffs(p, lin_coef, const_val):
    """Compute the L-polynomial of A_new for C: w^4 = x^3 + lin*x + const over F_p, F_p^2, F_p^3.
    Returns (e1, e2, e3, e4=p^2) via Newton's identities from a_k = #E(F_{p^k}) - #C(F_{p^k})."""
    results = []
    for k in range(1, 4):
        fk = make_field(p, k)
        Nk = p**k
        Ck = count_points(fk, Nk - 1, lin_coef, const_val, True)
        Ek = count_points(fk, Nk - 1, lin_coef, const_val, False)
        ak = Ek - Ck  # trace of new part
        results.append(ak)
    a1, a2, a3 = results
    # Newton's identities: power sums -> elementary symmetric
    e1 = a1
    e2 = (e1 * a1 - a2) // 2
    e3 = (a3 - 3 * e1 * e2 + e1**3) // (-6)  # wait, let me be more careful
    # Actually for 4 roots alpha_1..alpha_4:
    # a_k = sum alpha_i^k (power sums of reciprocal roots of L(T))
    # Newton: a1 = e1, a2 = e1*a1 - 2*e2, a3 = e1*a2 - e2*a1 + 3*e3
    # So: e1 = a1, e2 = (e1*a1 - a2)/2, e3 = (e1*a2 - e2*a1 + a3) ... wait
    # Let me just use the standard:
    # s1 = e1
    # s2 = s1*e1 - 2*e2  => e2 = (s1*e1 - s2)/2
    # s3 = s2*e1 - s1*e2 + 3*e3  => e3 = (s3 - s2*e1 + s1*e2)/3
    e1 = a1
    e2 = (a1 * e1 - a2) // 2
    e3 = (a3 - a2 * e1 + a1 * e2) // 3
    e4 = p * p
    return e1, e2, e3, e4

def format_Lpoly(e1, e2, e3, e4):
    """L(T) = e4*T^4 - e3*T^3 + e2*T^2 - e1*T + 1 ... actually let me check convention.
    Standard: L(T) = 1 + e1*T + e2*T^2 + e3*T^3 + e4*T^4  where e4=p^2.
    Wait, the document uses L(T) = p^2*T^4 + c3*T^3 + c2*T^2 + c1*T + 1.
    Let me just return the coefficients and check against the document."""
    # Document format: L_new(T) = p^2 T^4 + c3 T^3 + c2 T^2 + c1 T + 1
    # The relationship: if alpha_i are the reciprocal roots, then
    # L(T) = prod(1 - alpha_i T) = 1 - e1 T + e2 T^2 - e3 T^3 + e4 T^4
    # But document writes with positive leading coeff p^2 T^4 + ... + 1
    # That's the REVERSED polynomial: T^4 * L(1/T) = e4 - e3/T + e2/T^2 - e1/T^3 + 1/T^4
    # No wait: L(T) = prod(1 - alpha_i T). The reversed poly is T^4 L(1/T) = prod(T - alpha_i^{-1}) * ... hmm.
    # Let me just output both forms and compare with document.
    return e1, e2, e3, e4

print("=" * 60)
print("VERIFICATION: splitting-field-and-galois-audit-non-cm-v2.md")
print("=" * 60)

# === p = 13 (ordinary, 13 ≡ 1 mod 12) ===
p = 13
print(f"\n--- p = {p} (p mod 12 = {p % 12}) ---")

for a in range(1, p):
    e1, e2, e3, e4 = compute_Lnew_coeffs(p, 0, a)
    # L(T) = 1 - e1*T + e2*T^2 - e3*T^3 + e4*T^4
    # Document's format: p^2*T^4 + c3*T^3 + c2*T^2 + c1*T + 1
    # So c3 = -e3, c2 = e2, c1 = -e1 ... wait that's the reversal
    # Actually: p^2 T^4 + ... + 1 = e4 T^4 - e3 T^3 + e2 T^2 - e1 T + 1
    # Let me verify: for a=1, doc says 169T^4 + 104T^3 + 42T^2 + 8T + 1
    # That would be e4=169, -e3=104 => e3=-104, e2=42, -e1=8 => e1=-8
    # Let's check: is e1 the sum of reciprocal roots? For a=1 at p=13...

    # Try: is perfect square? Check if (e1^2 - 4*e2 + 8*p) == ...
    # Actually let's just check numerically by trying to factor
    # L(T) = e4*T^4 + (-e3)*T^3 + e2*T^2 + (-e1)*T + 1
    # Check if this equals (sqrt(e4)*T^2 + b*T + 1)^2 = e4*T^4 + 2b*sqrt(e4)*T^3 + (b^2+2*sqrt(e4))*T^2 + 2b*T + 1
    # So: -e3 = 2*b*p, e2 = b^2 + 2*p, -e1 = 2*b
    # From -e1 = 2b: b = -e1/2
    # Check: -e3 = 2*(-e1/2)*p = -e1*p  => e3 = e1*p
    # Check: e2 = (-e1/2)^2 + 2*p = e1^2/4 + 2*p

    is_cr = pow(a, (p-1)//3, p) == 1

    # Check perfect-square conditions
    b_cand = -e1 / 2 if e1 % 2 == 0 else None
    ps_check = False
    if b_cand is not None:
        b = int(b_cand)
        ps_check = (e3 == e1 * p) and (e2 == b*b + 2*p)

    status = "PERFECT SQUARE" if ps_check else "not perfect square"
    cr_label = "cubic residue" if is_cr else "non-cubic residue"

    print(f"  a={a:2d} ({cr_label:18s}): e1={e1:5d} e2={e2:5d} e3={e3:7d} e4={e4:6d}  "
          f"L = {e4}T^4 + {-e3}T^3 + {e2}T^2 + {-e1}T + 1  [{status}]")

# Verify specific document claims
print("\n--- Checking document's specific L-polynomials at p=13 ---")
doc_claims = {
    1: (169, 104, 42, 8),   # 169T^4 + 104T^3 + 42T^2 + 8T + 1 = (13T^2+4T+1)^2
    5: (169, -156, 62, -12), # (13T^2 - 6T + 1)^2
    8: (169, 156, 62, 12),   # (13T^2 + 6T + 1)^2
    12: (169, -104, 42, -8), # (13T^2 - 4T + 1)^2
    2: (169, 78, 23, 6),     # irreducible over Q
    3: (169, -52, 3, -4),    # irreducible over Q
}

for a, (d4, d3, d2, d1) in doc_claims.items():
    e1, e2, e3, e4 = compute_Lnew_coeffs(p, 0, a)
    # My format: L = e4*T^4 - e3*T^3 + e2*T^2 - e1*T + 1
    # Doc format: L = d4*T^4 + d3*T^3 + d2*T^2 + d1*T + 1
    # So: d4=e4, d3=-e3, d2=e2, d1=-e1
    match = (e4 == d4 and -e3 == d3 and e2 == d2 and -e1 == d1)
    print(f"  a={a}: doc says {d4}T^4 + {d3}T^3 + {d2}T^2 + {d1}T + 1  ->  {'MATCH' if match else 'MISMATCH'}")
    if not match:
        print(f"         got: {e4}T^4 + {-e3}T^3 + {e2}T^2 + {-e1}T + 1")

# === Non-CM control: w^4 = x^3 + x + 3 at p=13 ===
print(f"\n--- Non-CM control: w^4 = x^3 + x + 3 at p=13 ---")
e1, e2, e3, e4 = compute_Lnew_coeffs(13, 1, 3)
b_cand = -e1 / 2 if e1 % 2 == 0 else None
ps_check = False
if b_cand is not None:
    b = int(b_cand)
    ps_check = (e3 == e1 * p) and (e2 == b*b + 2*p)
print(f"  e1={e1} e2={e2} e3={e3} e4={e4}")
print(f"  L = {e4}T^4 + {-e3}T^3 + {e2}T^2 + {-e1}T + 1")
print(f"  Doc claims: 169T^4 + 104T^3 + 13T^2 + 8T + 1")
doc_match = (e4 == 169 and -e3 == 104 and e2 == 13 and -e1 == 8)
print(f"  Match: {doc_match}")
print(f"  Perfect square over Q: {ps_check}")

# === Now test the CUBIC BASE CHANGE perfect-square claim ===
# For non-cubic-residue a=2 at p=13, L_new is irreducible over Q.
# But after cubing the roots, the document claims it becomes a perfect square.
# To test this, compute L_new at p^3 = 2197 directly.
print(f"\n--- Cubic base-change test: a=2 at p=13 ---")
print(f"  Computing point counts at p=13, p^2=169, p^3=2197...")

# We need F_{13}, F_{13^2}, F_{13^3} point counts for BOTH w^4=x^3+2 and y^2=x^3+2
# But also F_{13^3}, F_{13^6}, F_{13^9} to get the base-changed L-poly!
# Actually the base-changed L-polynomial's coefficients come from:
# The original Frobenius eigenvalues alpha_i satisfy L_new(T)=0.
# The base-changed eigenvalues are alpha_i^3.
# So we need the power sums of alpha_i^3, alpha_i^6, alpha_i^9...
# which are the traces at F_{p^3}, F_{p^6}, F_{p^9}.
# That's computationally expensive. Let me do it via the roots numerically instead.

import numpy as np

def Lnew_basechange_check(p, lin, const):
    """Compute L_new, find roots, cube them, check if the cubed-root poly is a perfect square."""
    e1, e2, e3, e4 = compute_Lnew_coeffs(p, lin, const)
    # L(T) = e4 T^4 - e3 T^3 + e2 T^2 - e1 T + 1
    coeffs = [e4, -e3, e2, -e1, 1]
    roots = np.roots(coeffs)
    # These are roots of L(T) = 0, i.e. T_i = 1/alpha_i
    # Reciprocal roots = alpha_i = 1/T_i
    alphas = 1.0 / roots

    # Cube the alphas
    cubed = alphas ** 3

    # Build the polynomial from cubed roots: prod(T - cubed_i)
    poly = np.poly(cubed)  # leading coeff 1

    # Check if it's a perfect square: degree 4 poly = (degree 2)^2
    # If so, the 4 cubed roots consist of 2 pairs of equal values
    cubed_sorted = sorted(cubed, key=lambda z: (z.real, z.imag))

    print(f"  Original L: {e4}T^4 + {-e3}T^3 + {e2}T^2 + {-e1}T + 1")
    print(f"  Frobenius eigenvalues (alpha): {alphas}")
    print(f"  Cubed eigenvalues: {cubed}")

    # Check pairwise: are there exactly 2 distinct values each with multiplicity 2?
    tol = 1e-6
    pairs_found = 0
    used = [False]*4
    for i in range(4):
        if used[i]: continue
        for j in range(i+1, 4):
            if not used[j] and abs(cubed[i] - cubed[j]) < tol * max(1, abs(cubed[i])):
                pairs_found += 1
                used[j] = True
                break
        used[i] = True

    is_ps = (pairs_found == 2)
    print(f"  Cubed eigenvalue pairs: {pairs_found} pairs -> perfect square: {is_ps}")
    return is_ps

# CM cases
print("\nCM curves w^4 = x^3 + a at p=13:")
for a in [1, 2, 3, 5, 8, 12]:
    is_cr = pow(a, (13-1)//3, 13) == 1
    print(f"\n  a={a} ({'cubic res' if is_cr else 'non-cubic res'}):")
    Lnew_basechange_check(13, 0, a)

# Non-CM control
print(f"\nNon-CM control w^4 = x^3 + x + 3 at p=13:")
Lnew_basechange_check(13, 1, 3)

# Also test at p=43 (p ≡ 7 mod 12, supersingular)
print(f"\n\n--- Supersingular regime: p=43 (43 mod 12 = 7) ---")
for a in [1, 2, 3]:
    is_cr = pow(a, (43-1)//3, 43) == 1
    print(f"\n  a={a} ({'cubic res' if is_cr else 'non-cubic res'}):")
    Lnew_basechange_check(43, 0, a)

print(f"\nNon-CM control w^4 = x^3 + x + 3 at p=43:")
Lnew_basechange_check(43, 1, 3)
