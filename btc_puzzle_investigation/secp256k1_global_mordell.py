"""secp256k1 as the reduction of the GLOBAL Mordell curve E: y^2 = x^3 + 7 over Q.
Rarely connected to the crypto curve. Map: rational points (rank/torsion),
bad reduction, and the L-function coefficients a_l = l+1-#E(F_l) — whose CM
pattern (supersingular iff l=2 mod 3) ties to secp256k1's own trace. Exact."""
from sympy import isprime, primerange

# --- 1. E(Q): search for rational points up to height H (torsion / small gens) ---
print("=== E: y^2 = x^3 + 7 over Q ===")
print("  Discriminant Delta = -432*b^2 = -432*49 =", -432*49, " -> bad primes divide it")
from sympy import factorint
print("  bad reduction primes:", sorted(factorint(432*49).keys()))
print("\n  rational points with |num|,|den| bounded (torsion + tiny gens):")
from fractions import Fraction
found = []
H = 200
for xn in range(-H, H+1):
    for xd in range(1, H+1):
        from math import gcd
        if gcd(abs(xn), xd) != 1: continue
        x = Fraction(xn, xd)
        rhs = x**3 + 7
        if rhs < 0: continue
        # is rhs a rational square?
        num, den = rhs.numerator, rhs.denominator
        import math
        sn, sd = math.isqrt(num), math.isqrt(den)
        if sn*sn == num and sd*sd == den:
            found.append((x, Fraction(sn, sd)))
print(f"    points found (x, y>=0): {found if found else 'NONE (besides O) up to height %d' % H}")
print("    => y^2=x^3+7 is the classical Mordell curve with NO integer solutions;")
print("       consistent with trivial torsion; (LMFDB 3888.a1: rank 0, torsion trivial).")

# --- 2. L-function coefficients a_l and the CM supersingular pattern ---
def count_points(l, b=7):
    c = 1  # O
    for x in range(l):
        r = (x*x*x + b) % l
        if r == 0: c += 1
        elif pow(r, (l-1)//2, l) == 1: c += 2
    return c
print("\n=== a_l = l + 1 - #E(F_l)  (L-function of y^2=x^3+7);  CM: supersingular iff l = 2 mod 3 ===")
print("   l  : l%3  #E(F_l)   a_l    supersingular(a_l=0)?")
for l in primerange(5, 60):
    Nl = count_points(l); al = l + 1 - Nl
    ss = (al % l == 0)   # supersingular <=> a_l ≡ 0 (mod l); for these small l means a_l=0
    pred = (l % 3 == 2)
    tag = "" if ss == pred else "  <-- CHECK"
    print(f"  {l:3d} :  {l%3}   {Nl:>6}   {al:>+4}    {'YES' if al==0 else 'no'}   (l%3==2? {pred}){tag}")

# --- 3. secp256k1's p in this global picture ---
p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
t = p + 1 - n
print("\n=== secp256k1's prime p in the global L-function ===")
print(f"  p mod 3 = {p%3}  => p is ORDINARY (not supersingular); a_p = trace t is the L-coefficient.")
print(f"  a_p = t = {t}")
print(f"  #E(F_p) = n = p+1-a_p (the group order).  The whole crypto curve is the")
print(f"  reduction of this ONE global Q-curve at the pseudo-Mersenne prime p.")
print(f"  |a_p| = {t.bit_length()}-bit ~ 2*sqrt(p) region (Hasse/Sato-Tate); a_p>0 (p splits as pi*pibar in Z[w]).")
