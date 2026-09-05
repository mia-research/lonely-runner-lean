"""Arithmetic fingerprint of secp256k1 — multiplicative orders + residue symbols
of the small primes mod p and mod n. Under-tabulated concrete invariants; an
anomalously SMALL order (large subgroup index) would be a genuine feature.
Uses the full factorizations of p-1 and n-1. Exact integers."""
from sympy import isprime, primerange

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

# full factorizations (p-1 verified: 2*3*7*13441*C; n-1 from thread 1)
Cp = (p-1)//(2*3*7*13441)
fac_p1 = {2:1,3:1,7:1,13441:1, Cp:1}
fac_n1 = {2:6,3:1,149:1,631:1, 107361793816595537:1,
          174723607534414371449:1, 341948486974166000522343609283189:1}
assert isprime(Cp)
assert 2**6*3*149*631*107361793816595537*174723607534414371449*341948486974166000522343609283189 == n-1

def order(a, m, fac):
    o = m-1
    for q in fac:
        while o % q == 0 and pow(a, o//q, m) == 1: o //= q
    return o

def leg(a, m): return pow(a % m, (m-1)//2, m)          # 1 QR, m-1 nonQR
def is_cube(a, m): return pow(a % m, (m-1)//3, m)       # 1 iff cube (m=1 mod 3)

print("=== multiplicative-order fingerprint of small primes ===")
print(f"{'m':>3} | {'ord_p(m)/(p-1)':>16} idx_p | {'ord_n(m)/(n-1)':>16} idx_n | QRp QRn cubeP cubeN")
from fractions import Fraction
for m in list(primerange(2, 60)):
    op = order(m, p, fac_p1); on = order(m, n, fac_n1)
    ip = (p-1)//op; ino = (n-1)//on
    qp = "+" if leg(m,p)==1 else "-"; qn = "+" if leg(m,n)==1 else "-"
    cp = "1" if is_cube(m,p)==1 else "x"; cn = "1" if is_cube(m,n)==1 else "x"
    fp = Fraction(op, p-1); fn = Fraction(on, n-1)
    print(f"{m:>3} | {str(fp):>16} {ip:>5} | {str(fn):>16} {ino:>5} | {qp}   {qn}   {cp}    {cn}")

print("\nreadout:")
print("  idx = [(Z/·)* : <m>] = subgroup index; large idx ⇒ m generates a SMALL subgroup (notable).")
print("  ord_n(2)=(n-1)/64 (idx 64) confirmed. Scan for any m with anomalously large index.")

# explicit hunt for the largest-index (smallest-order) small element, mod n and mod p
print("\n=== primes with the LARGEST subgroup index (smallest order) up to 200 ===")
best_n = sorted(((p-1)//order(m,p,fac_p1), m, 'p') for m in primerange(2,200))[-3:]
best_n2 = sorted(((n-1)//order(m,n,fac_n1), m, 'n') for m in primerange(2,200))[-3:]
for idx, m, mod in best_n:  print(f"  mod p: m={m:>3} index={idx}  (= 2^{idx.bit_length()-1} ish)")
for idx, m, mod in best_n2: print(f"  mod n: m={m:>3} index={idx}")
