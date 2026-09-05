"""Atlas thread 1 (clean) — x-line doubling map phi2 as a dynamical system.
Core claim, verified: phi2 is "double the index" -- phi2(x(jG)) = x((2j)G).
Hence the phi2 functional graph on P^1(F_p) = (doubling on Z/n, folded by +-)
                                             ⊔ (doubling on Z/n', folded by +-).
Demonstrated on a small PRIME-order j=0 curve; then stated for secp256k1."""
from collections import Counter
from sympy import isprime, factorint

def pts_and_gen(p, b=7):
    pts = [None]
    for x in range(p):
        rhs = (x*x*x + b) % p
        for y in range(p):
            if (y*y) % p == rhs: pts.append((x, y))
    return pts

def ec_add(P, Q, p, b=7):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    m = (3*x1*x1)*pow(2*y1, -1, p) % p if P == Q else (y2-y1)*pow((x2-x1) % p, -1, p) % p
    x3 = (m*m - x1 - x2) % p
    return (x3, (m*(x1 - x3) - y1) % p)

def phi2(x, p, b=7):
    if x is None: return None
    den = 4*(x*x*x + b) % p
    return None if den == 0 else (x*x*x*x - 8*b*x)*pow(den, -1, p) % p

def cycles(p, b=7):
    seen = set(); out = []
    for s in list(range(p)) + [None]:
        if s in seen: continue
        path = []; x = s
        while x not in seen and x not in path:
            path.append(x); x = phi2(x, p, b)
        if x in path: out.append(len(path) - path.index(x))
        seen.update(path)
    return sorted(out)

def mult_order(a, m):
    o = m - 1
    for q in factorint(m-1):
        while o % q == 0 and pow(a, o // q, m) == 1: o //= q
    return o

# find a small prime-order j=0 curve (p0 ≡ 1 mod 3, like secp256k1)
p0 = None
for cand in range(50, 400):
    if cand % 3 != 1 or not isprime(cand): continue
    n0 = len(pts_and_gen(cand))
    if isprime(n0): p0 = cand; break
pts = pts_and_gen(p0); n0 = len(pts); np0 = 2*p0 + 2 - n0
print(f"=== small PRIME-order j=0 curve y^2=x^3+7 / F_{p0} (p0%3={p0%3}) ===")
print(f"  n0=#E={n0} (prime {isprime(n0)}),  twist n0'={np0} (prime {isprime(np0)})")

# a generator G (order n0, prime => any non-O point)
G = next(P for P in pts if P is not None)
mult = [None]*(n0); cur = None
for j in range(n0): mult[j] = cur; cur = ec_add(cur, G, p0)
xof = {j: (mult[j][0] if mult[j] else None) for j in range(n0)}

# CORE VERIFICATION: phi2(x(jG)) == x((2j mod n0) G) for every j
ok = all(phi2(xof[j], p0) == xof[(2*j) % n0] for j in range(n0))
print(f"  CORE: phi2(x(jG)) == x((2j)G) for all j ?  {ok}   (phi2 = double-the-index)")

# cycle structure of phi2 and the prediction from doubling on Z/n0, Z/n0'
cyc = cycles(p0)
o_c = mult_order(2, n0); o_t = mult_order(2, np0)
neg1_is_pow2_c = pow(2, o_c // 2, n0) == n0 - 1 if o_c % 2 == 0 else False
neg1_is_pow2_t = pow(2, o_t // 2, np0) == np0 - 1 if o_t % 2 == 0 else False
fold_c = o_c // 2 if neg1_is_pow2_c else o_c
fold_t = o_t // 2 if neg1_is_pow2_t else o_t
print(f"  phi2 cycle lengths on P^1 ({p0+1} nodes): {dict(Counter(cyc))}")
print(f"  ord_n0(2)={o_c} (folded curve cycle -> {fold_c});  ord_n0'(2)={o_t} (folded twist -> {fold_t})")
print(f"  fixed points (len-1 cycles) = O plus F_p-rational 3-torsion x-coords: {cyc.count(1)}")

print(f"\n=== secp256k1 ===")
p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
npr = 2*p + 2 - n
print(f"  phi2(x)=(x^4-56x)/(4(x^3+7)); it is 'double the index' on E(F_p)=Z/n and on E'(F_p)=Z/n'.")
print(f"  => phi2's whole P^1(F_p) orbit structure is fixed by two numbers: ord_n(2) and ord_n'(2).")
print(f"  fixed pts: x=inf (=O) + the 4 three-torsion x-coords (F_p-rational; they are TWIST 3-torsion, 3^2|n').")
print(f"  n'  = 2p+2-n small factors include 3^2*13^2 (atlas v1).")
print(f"  ord_n(2), ord_n'(2) need n-1, n'-1 factored (256-bit) -> next: factor those to pin the cycle lengths.")
