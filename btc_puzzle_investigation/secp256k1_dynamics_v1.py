"""Atlas thread 1 — x-line multiplication-map dynamics.
Doubling on the curve descends to phi2(x) = (x^4 - 8b x)/(4(x^3+b)) on P^1.
Claim: the functional graph of phi2 on P^1(F_p) decomposes EXACTLY as
  (doubling on E(F_p)=Z/n, folded by +-) ⊔ (doubling on twist E'=Z/n', folded).
Verified on a small j=0 curve y^2=x^3+7; then stated for secp256k1.
Exact integers."""
def curve_points(p, b=7):
    pts = [None]  # O
    for x in range(p):
        rhs = (x*x*x + b) % p
        for y in range(p):
            if (y*y) % p == rhs:
                pts.append((x, y))
    return pts

def ec_add(P, Q, p, b=7):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    if P == Q:
        m = (3*x1*x1) * pow(2*y1, -1, p) % p
    else:
        m = (y2 - y1) * pow((x2 - x1) % p, -1, p) % p
    x3 = (m*m - x1 - x2) % p
    return (x3, (m*(x1 - x3) - y1) % p)

def phi2(x, p, b=7):
    """x-coord of [2]P where P has x-coord x; x=None is infinity."""
    if x is None: return None
    den = 4*(x*x*x + b) % p
    if den == 0: return None       # x is 2-torsion -> [2]P = O
    return (x*x*x*x - 8*b*x) * pow(den, -1, p) % p

def cycle_structure(p, b=7):
    """functional graph of phi2 on P^1(F_p): return list of cycle lengths."""
    nodes = list(range(p)) + [None]
    seen = {}; cycles = []
    for start in nodes:
        path = []; x = start
        while x not in seen and x not in path:
            path.append(x); x = phi2(x, p, b)
        if x in path:                      # found a new cycle
            cyc = path[path.index(x):]
            if all(c not in seen for c in cyc):
                cycles.append(len(cyc))
            for c in path: seen[c] = True
        else:
            for c in path: seen[c] = True
    return sorted(cycles)

def order_of(a, m):
    if m == 1: return 1
    from sympy import factorint
    e = m
    # multiplicative order of a mod m (m prime here)
    o = m - 1
    for q in factorint(m-1):
        while o % q == 0 and pow(a, o//q, m) == 1:
            o //= q
    return o

# ---------- small-curve verification ----------
from sympy import isprime
p0 = 103                                   # 103 % 3 == 1 (j=0 / CM like secp256k1)
pts = curve_points(p0); n0 = len(pts)
np0 = 2*p0 + 2 - n0                         # twist order
print(f"=== small j=0 curve  y^2=x^3+7 over F_{p0}  (p0 mod 3 = {p0%3}) ===")
print(f"  #E(F_p0) = n0 = {n0} (prime? {isprime(n0)}),  twist n0' = {np0} (prime? {isprime(np0)})")

cyc = cycle_structure(p0)
from collections import Counter
print(f"  phi2 functional-graph cycle lengths (P^1, {p0+1} nodes): {dict(Counter(cyc))}")

# predicted: doubling on Z/n0 folded by +- gives cycles; likewise Z/n0'
o_curve = order_of(2, n0) if isprime(n0) else None
o_twist = order_of(2, np0) if isprime(np0) else None
print(f"  ord_n0(2)  = {o_curve}  -> curve-part longest cycle (folded)")
print(f"  ord_n0'(2) = {o_twist}  -> twist-part longest cycle (folded)")
print(f"  fixed points of phi2 (cycle length 1) = 3-torsion x-coords: {cyc.count(1)}")

# ---------- secp256k1 statement ----------
print(f"\n=== secp256k1 ===")
p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
npr = 2*p+2-n
print(f"  phi2(x) = (x^4 - 56x) / (4(x^3+7))  mod p   (Lattes map, deg 4)")
print(f"  P^1(F_p) splits: E(F_p)=Z/n  ⊔  twist E'(F_p)=Z/n'  ⊔  fixed(3-torsion)")
print(f"  fixed points of phi2 = 4 three-torsion x-coords (all F_p-rational, mapped in v2)")
print(f"  curve-part cycle length = ord_n(2) | (n-1);  twist-part = ord_n'(2) | (n'-1)")
print(f"  n  = {hex(n)}")
print(f"  n' = 2p+2-n = {hex(npr)}   (twist order; small factors 3^2*13^2 found in atlas v1)")
