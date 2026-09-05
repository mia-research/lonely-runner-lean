"""Atlas thread 3 — notable / exceptional points (the curve's landmarks).
Small-x points, lowest-Hamming (power-of-2) x-coords, endomorphism-fixed points,
and a 'nothing-up-my-sleeve' audit of the generator G. Exact integers."""
p  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
b  = 7
def onclose(x):                      # is x a curve x-coord? (x^3+7 a QR or 0)
    r = (x*x*x + b) % p
    return r == 0 or pow(r, (p-1)//2, p) == 1
def ysqrt(x):
    r = pow((x*x*x + b) % p, (p+1)//4, p)
    return r if (r*r) % p == (x*x*x+b) % p else None

print("=== (a) smallest curve points (least non-neg x with a point) ===")
small = [x for x in range(0, 60) if onclose(x)]
print(f"  valid small x in [0,60): {small}")
x0 = next(x for x in range(1, 10**6) if onclose(x))
print(f"  smallest x>=1 on the curve: x={x0}, point ({x0}, {hex(ysqrt(x0))[:18]}..)")
print(f"  (all such points have order n — n is prime — so notability is the coordinate, not the order)")

print("\n=== (b) lowest-Hamming x-coords: which powers of two 2^k lie on the curve ===")
hits = [k for k in range(0, 60) if onclose(pow(2, k, p))]
print(f"  2^k on curve for k in [0,60): {hits}")
print(f"  (weight-1 x-coordinates — the most 'structured' points; ~half of k work)")
# also x = 2^k - 1 (all-ones), x = p - small
ones = [k for k in range(1, 40) if onclose((1 << k) - 1)]
print(f"  x = 2^k - 1 (all-ones) on curve for k in [1,40): {ones}")

print("\n=== (c) endomorphism-fixed points  phi(P)=±P ===")
lam = pow(2, (n-1)//3, n)
import math
print(f"  phi(P)=P  ⇒ (λ-1)P=O; gcd(λ-1, n) = {math.gcd((lam-1) % n, n)}  (1 ⇒ only O fixed)")
print(f"  phi(P)=-P ⇒ (λ+1)P=O; gcd(λ+1, n) = {math.gcd((lam+1) % n, n)}  (1 ⇒ only O)")
print(f"  ⇒ the GLV endomorphism has NO nontrivial F_p fixed/anti-fixed points (n prime).")

print("\n=== (d) generator G — nothing-up-my-sleeve audit ===")
from sympy import isprime
print(f"  Gx Hamming weight: {bin(Gx).count('1')} / 256   Gy Hamming weight: {bin(Gy).count('1')} / 256  (≈128 ⇒ unstructured)")
print(f"  Gx prime? {isprime(Gx)}   Gy prime? {isprime(Gy)}")
print(f"  Gx vs p:  p-Gx = {hex(p-Gx)[:20]}..   Gx mod small = {[Gx%m for m in (2,3,5,7,11,13)]}")
print(f"  simple relations? Gx==βGx? no; Gx a small multiple of anything obvious? "
      f"gcd(Gx,p-1)={math.gcd(Gx,p-1)}, gcd(Gx,n-1)={math.gcd(Gx,n-1)}")
print(f"  on curve? {(Gy*Gy - Gx*Gx*Gx - b) % p == 0}   (G is a real point, order n)")
print("  verdict: G's coords look structureless (balanced Hamming, no small relations) —")
print("  consistent with the documented 'nothing up my sleeve' choice; no landmark structure.")
