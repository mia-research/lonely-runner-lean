#!/usr/bin/env python3
"""Verify the exact Lean-side witness formulas for bhk_s7_exc_table9.

Window (bhk_s7_witness_num): with a, b the residues of (c3*k, c1*k) mod n:
  n <= 6a <= 5n  and  n + 3a <= 9b <= 5n + 3a.
"""
from math import gcd

def window(a, b, n):
    return n <= 6*a <= 5*n and n + 3*a <= 9*b <= 5*n + 3*a

def check_formula(name, nrange, mf, af, bf, side):
    fails = []
    for n in nrange:
        m = mf(n)
        if not side(n, m):
            fails.append((n, m, 'side'))
            continue
        if not window(af(n, m), bf(n, m), n):
            fails.append((n, m, 'window'))
    print(f"{name}: {'OK' if not fails else 'FAILS ' + str(fails[:10])}")

R = range(7, 5001)
# (3,1) and (3,-1): m = (7n+17)/18, a = 3m-n (q=1), b = m resp. n-m
check_formula("(3,+1) m=(7n+17)/18", R, lambda n: (7*n+17)//18,
              lambda n, m: 3*m-n, lambda n, m: m,
              lambda n, m: 1 <= m < n and n <= 3*m < 2*n)
check_formula("(3,-1) m=(7n+17)/18", R, lambda n: (7*n+17)//18,
              lambda n, m: 3*m-n, lambda n, m: n-m,
              lambda n, m: 1 <= m and 1*m < n and n <= 3*m < 2*n)
# (4,1): m = (7n+23)/24, a = 4m-n, b = m
check_formula("(4,+1) m=(7n+23)/24", R, lambda n: (7*n+23)//24,
              lambda n, m: 4*m-n, lambda n, m: m,
              lambda n, m: 1 <= m < n and n <= 4*m < 2*n)
# (4,-1): m = (n+2)/3, a = 4m-n, b = n-m
check_formula("(4,-1) m=(n+2)/3", R, lambda n: (n+2)//3,
              lambda n, m: 4*m-n, lambda n, m: n-m,
              lambda n, m: 1 <= m and m < n and n <= 4*m < 2*n)
# (3,2): m = (13n+17)/18, a = 3m-2n, b = 2m-n
check_formula("(3,+2) m=(13n+17)/18", R, lambda n: (13*n+17)//18,
              lambda n, m: 3*m-2*n, lambda n, m: 2*m-n,
              lambda n, m: 2*n <= 3*m < 3*n and n <= 2*m < 2*n)
# (3,-2): n >= 8: m = (4n+26)/27, a = 3m (<n), b = n-2m (2m<n)
check_formula("(3,-2) n>=8 m=(4n+26)/27", range(8, 5001), lambda n: (4*n+26)//27,
              lambda n, m: 3*m, lambda n, m: n-2*m,
              lambda n, m: 1 <= m and 3*m < n and 2*m < n)
# (4,2): n >= 24: m = (n+5)/6, a = 4m, b = 2m
check_formula("(4,+2) n>=24 m=(n+5)/6", range(24, 5001), lambda n: (n+5)//6,
              lambda n, m: 4*m, lambda n, m: 2*m,
              lambda n, m: 1 <= m and 4*m < n and 2*m < n)
# (4,-2): n >= 13: m = (2n+14)/15, a = 4m, b = n-2m
check_formula("(4,-2) n>=13 m=(2n+14)/15", range(13, 5001), lambda n: (2*n+14)//15,
              lambda n, m: 4*m, lambda n, m: n-2*m,
              lambda n, m: 1 <= m and 4*m < n and 2*m < n)

print("\n== per-n witnesses for (4,2) n in 9..23 (skip 14) and (4,-2) n in {7,9..12} ==")
for (i, j, ns) in [(4, 2, [n for n in range(9, 24) if n != 14]), (4, -2, [7, 9, 10, 11, 12])]:
    for n in ns:
        got = None
        for m in range(1, n):
            a, b = (i*m) % n, (j*m) % n
            if window(a, b, n):
                got = (m, a, b)
                break
        print(f"  (i,j)=({i},{j}), n={n}: m,a,b = {got}")

print("\n== decide statements ==")
def decide_stmt(n, ares, bres):
    for A in range(n):
        for B in range(n):
            for K in range(n):
                if (A*K) % n == ares and (B*K) % n == bres and gcd(n, gcd(A, B)) == 1:
                    if not any(window((A*t) % n, (B*t) % n, n) for t in range(n)):
                        return False, (A, B, K)
    return True, None
print("n=8, (4,2): A*K%8=4, B*K%8=2:", decide_stmt(8, 4, 2))
print("n=8, (4,-2): A*K%8=4, B*K%8=6:", decide_stmt(8, 4, 6))
print("n=14, (4,2): A*K%14=4, B*K%14=2:", decide_stmt(14, 4, 2))

print("\n== fibre construction check: i in {2,3,4}, i|n: x = lo + ((a0+(i-1)*lo)%i), lo=(n+5)/6, w = n/2 (i even) or n/3 ==")
fails = []
for i in (2, 3, 4):
    for n in range(7, 2000):
        if n % i:
            continue
        w = n // 2 if i % 2 == 0 else n // 3
        lo = (n + 5) // 6
        for a0 in range(n):
            x = lo + ((a0 + (i-1)*lo) % i)
            if x % i != a0 % i or not (x < n) or not window(x, w, n):
                fails.append((i, n, a0, x))
print("fibre:", "OK" if not fails else f"FAILS {fails[:10]}")

print("\n== minimality witnesses at n=7: (3,-2): 3*(3,-2) ; (4,2): 3*(4,2) ==")
print("  (3,-2) n=7: residues of 3*k0:", ((3*3) % 7, ((7-2)*3) % 7), "-> kl=(2,1)")
print("  (4,2) n=7: residues of 3*k0:", ((4*3) % 7, (2*3) % 7), "-> kl=(-2,-1) via offsets -1,-1")
