"""Genuinely-unpredictable experiment: is there ANY hidden small-coefficient exact
relation among secp256k1's constants (over Z, mod p, mod n) beyond the known
identities? I cannot predict the outcome. Exact-fraction LLL for integer-relation
detection; every candidate verified exactly; known identities filtered out."""
from fractions import Fraction as Fr

def dot(u, v): return sum(a*b for a, b in zip(u, v))
def lll(B, delta=Fr(3, 4)):
    B = [list(map(Fr, row)) for row in B]
    m = len(B)
    def gs():
        Bs = []; mu = [[Fr(0)]*m for _ in range(m)]
        for i in range(m):
            bi = list(B[i])
            for j in range(i):
                mu[i][j] = dot(B[i], Bs[j]) / dot(Bs[j], Bs[j])
                bi = [bi[k] - mu[i][j]*Bs[j][k] for k in range(len(bi))]
            Bs.append(bi)
        return Bs, mu
    Bs, mu = gs()
    k = 1
    while k < m:
        for j in range(k-1, -1, -1):
            q = round(mu[k][j])
            if q != 0:
                B[k] = [B[k][t] - q*B[j][t] for t in range(len(B[k]))]
                Bs, mu = gs()
        if dot(Bs[k], Bs[k]) >= (delta - mu[k][k-1]**2)*dot(Bs[k-1], Bs[k-1]):
            k += 1
        else:
            B[k], B[k-1] = B[k-1], B[k]
            Bs, mu = gs()
            k = max(k-1, 1)
    return [[int(x) for x in row] for row in B]

def find_relations(names, vals, cmax=6, weight_bits=None, mod=None):
    """small integer relations sum c_i v_i == 0  (exact, or ==0 mod `mod`)."""
    k = len(vals)
    V = [v % mod if mod else v for v in vals]
    maxbits = max(1, max(abs(v).bit_length() for v in V))
    W = 1 << (maxbits + 40)
    basis = [[ (W*V[i] if j == k else (1 if j == i else 0)) for j in range(k+1)] for i in range(k)]
    red = lll(basis)
    rels = []
    for row in red:
        coeffs = row[:k]
        if all(c == 0 for c in coeffs): continue
        if max(abs(c) for c in coeffs) > cmax: continue
        s = sum(c*v for c, v in zip(coeffs, vals))
        if (s % mod == 0) if mod else (s == 0):
            rels.append(coeffs)
    return rels

# validate LLL on a known relation: 2*6 - 3*4 == 0 among {6,4,10}
print("LLL sanity:", find_relations(["6","4"], [6, 4], cmax=6), "(expect a mult of [2,-3])")

p  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
import math
t = p+1-n; f = math.isqrt((4*p-t*t)//3); a = (t+f)//2; b = f
beta = pow(3, (p-1)//3, p); lam = pow(2, (n-1)//3, n)

def report(title, names, vals, mod=None, cmax=6):
    print(f"\n=== {title} ===")
    rels = find_relations(names, vals, cmax=cmax, mod=mod)
    if not rels:
        print("  no small-coefficient relation found")
        return
    for c in rels:
        expr = " + ".join(f"{ci}*{nm}" for ci, nm in zip(c, names) if ci != 0)
        print(f"  {expr} == 0" + (f" (mod {'p' if mod==p else 'n'})" if mod else " (over Z)"))

# Over Z: linear among the CM constants (+ squares to catch quadratics)
report("over Z: {1, p, n, t, f}", ["1","p","n","t","f"], [1, p, n, t, f])
report("over Z: {p, t^2, f^2, t, f, 1}", ["p","t^2","f^2","t","f","1"], [p, t*t, f*f, t, f, 1])
report("over Z: {p, a^2, ab, b^2, a, b, 1}", ["p","a^2","ab","b^2","a","b","1"], [p, a*a, a*b, b*b, a, b, 1])
report("over Z: {1,p,n,t,f,Gx,Gy}  (does the generator relate?)",
       ["1","p","n","t","f","Gx","Gy"], [1, p, n, t, f, Gx, Gy])
# Mod p: does the generator satisfy a hidden linear/low-degree relation?
report("mod p: {1, Gx, Gy, beta, Gx^2, Gx*Gy}", ["1","Gx","Gy","beta","Gx^2","GxGy"],
       [1, Gx, Gy, beta, Gx*Gx % p, Gx*Gy % p], mod=p)
report("mod n: {1, lam, t, f, a, b}", ["1","lam","t","f","a","b"], [1, lam, t, f, a, b], mod=n)
