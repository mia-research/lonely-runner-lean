"""Atlas thread 2 — twist & isogeny structure.
(a) Twist order n'=2p+2-n and its F_p-rational torsion (small factors).
(b) # F_p-rational l-isogenies from E = #roots of x^2 - t x + p (mod l),
    which by CM (disc -3) is dictated purely by l mod 3.
(c) class number h(-3)=1 => degenerate isogeny volcano (crater only) => the
    earlier isogeny probe (Test C) had nothing to find. Exact integers."""
from sympy import isprime, factorint

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
t = p + 1 - n
np_ = 2*p + 2 - n                       # twist order = p+1+t

print("=== (a) quadratic twist E' : order n' = 2p+2-n ===")
def small_factor(m, bound=2_000_000):
    fac = {}
    for q in [2, 3, 5, 7, 11, 13] + list(range(17, bound, 2)):
        if q*q > m: break
        while m % q == 0: fac[q] = fac.get(q, 0)+1; m //= q
    return fac, m
fac, cof = small_factor(np_)
print(f"  n' = {np_}")
print(f"  small factors: {fac}   cofactor {cof.bit_length()}-bit prime? {isprime(cof)}")
print(f"  => E'(F_p) has F_p-rational torsion of orders: {sorted(set(q**e for q in fac for e in range(1,fac[q]+1)))[:8]} ...")
print(f"  (this is why the four 3-torsion x-coords are F_p-rational: 3^2 | n' ⇒ twist has 3- and 9-torsion)")

print("\n=== (b) # F_p-rational l-isogenies from E  vs  l mod 3  (CM disc -3) ===")
print("  l  : l%3  #roots(x^2-tx+p mod l)  predicted(2 if l≡1, 0 if l≡2, 1 if l=3)")
disc = t*t - 4*p                         # = -3 f^2
for l in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61]:
    nroots = sum(1 for x in range(l) if (x*x - t*x + p) % l == 0)   # roots mod l
    pred = 1 if l == 3 else (2 if l % 3 == 1 else 0)
    tag = "" if nroots == pred else "  <-- MISMATCH"
    print(f"  {l:3d} : {l%3:2d}       {nroots:2d}                     {pred}{tag}")

print("\n=== (c) class number of the CM order ===")
print("  End(E)=Z[omega], disc=-3, class number h(-3)=1.")
print("  => only ONE j-invariant (j=0) has CM by Z[omega]; the l-isogeny graph is a")
print("     degenerate 'volcano' — just the crater, no descent to smaller orders.")
print("  => an isogeny walk stays on j=0 twists; there is no hidden structure to")
print("     descend into. This is the structural reason Test C (isogeny probe) was null.")
print(f"  check: disc t^2-4p = -3*f^2 ?  { (4*p - t*t) % 3 == 0 and __import__('math').isqrt((4*p-t*t)//3)**2 == (4*p-t*t)//3 }")
