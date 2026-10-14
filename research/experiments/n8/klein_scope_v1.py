"""Guard.klein_self_inverse is stated at ZMod 8. The units of Z/n are ALL self-inverse
exactly when n | 24.  TwoPatterns.unit_on_both rests on u^2 = 1 mod 8.  So does the AP's
four-coincidence structure survive at other orders, or is it special?
"""
from math import gcd
print("1. is every unit of Z/n self-inverse?")
selfinv = []
for n in range(2, 60):
    us = [u for u in range(1, n) if gcd(u, n) == 1]
    if all((u*u) % n == 1 for u in us):
        selfinv.append(n)
print(f"   n with u^2 = 1 mod n for every unit u, n < 60: {selfinv}")
print(f"   divisors of 24: {[d for d in range(1,25) if 24 % d == 0]}")
print(f"   match: {selfinv == [d for d in range(2,25) if 24 % d == 0]}")

print("\n2. the AP coincidence at order n: is x = u on BOTH patterns?")
print(f"   (+1 via reading u needs u*u = 1 mod n;  -1 via reading n-u needs u(n-u) = -1 mod n)")
print(f"   {'n':>3}  {'units':<22} {'u*u=1 all?':>11} {'u(n-u)=-1 all?':>15}")
for n in (5, 6, 7, 8, 9, 11, 12, 13, 24):
    us = [u for u in range(1, n) if gcd(u, n) == 1]
    a = all((u*u) % n == 1 for u in us)
    b = all((u*(n-u)) % n == (n-1) for u in us)
    print(f"   {n:>3}  {str(us)[:22]:<22} {str(a):>11} {str(b):>15}")
print()
print("3. consequence: the four-coincidence structure of the AP is a fact about n | 24,")
print("   NOT about n = 8 as an order.  At n = 7, 9, 11, 13 the units are not self-inverse,")
print("   so x = u does not sit on the +1 pattern via reading u.")
