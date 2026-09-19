"""Deposit for the two general-n computations quoted in MANUSCRIPT_v13 section 14D and 14F:
  (1) the residues with L(b)+U(b) = b-1 are exactly {0,1} mod n, at every order;
  (2) b = 2 is the only modulus with L(b) = U(b), at every order.
"""
def I(b, n): return (-(-(b-1)//n), ((n-1)*b - 1)//n)
print("(1) residues b mod n with L(b)+U(b) = b-1   [the obstructed ones]")
bad_any = 0
for n in range(4, 14):
    obstructed = sorted({b % n for b in range(2, 40*n) if I(b,n)[0]+I(b,n)[1] == b-1})
    other = [b for b in range(2, 40*n) if I(b,n)[0]+I(b,n)[1] not in (b, b-1)]
    bad_any += len(other)
    print(f"    n={n:<3} {obstructed}" + (f"   OTHER SUMS: {other[:5]}" if other else ""))
print(f"    sums other than b or b-1, any order: {bad_any}")
print()
print("(2) degenerate moduli L(b) = U(b), b < 600")
for n in range(4, 14):
    print(f"    n={n:<3} {[b for b in range(2, 600) if I(b,n)[0] == I(b,n)[1]]}")
