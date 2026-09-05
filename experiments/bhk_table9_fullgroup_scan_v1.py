#!/usr/bin/env python3
"""For the unresolved (i,j,n) triples — (4,2,8), (4,2,14), (4,-2,8) — and for the
fibre cases (3,0) with 3|n, (4,0) with 4|n, (2,0) with 2|n, enumerate ALL valid
generator pairs (c3, c1) mod n satisfying:
  gcd(n, gcd(c3, c1)) = 1,  n does not divide c3 or c1,
  exists k0: (c3*k0, c1*k0) == (i, j mod n) (mod n),
and check whether the full cyclic group <(c3,c1)> contains
  (a) a witness-window element, or
  (b) a minimality-box element (contradicting minimality of (i,j)).
"""
from math import gcd

def balanced(r, n):
    r %= n
    return r if r <= n // 2 else r - n

def window_ok(a, b, n):
    return n <= 6 * a <= 5 * n and n + 3 * a <= 9 * b <= 5 * n + 3 * a

def check(i, j, n, verbose=False):
    jm = j % n
    bad = []
    for c3 in range(n):
        for c1 in range(n):
            if c3 % n == 0 or c1 % n == 0:
                continue
            if gcd(n, gcd(c3, c1)) != 1:
                continue
            if not any((c3 * k) % n == i % n and (c1 * k) % n == jm for k in range(n)):
                continue
            # full group elements
            found_window = None
            found_min = None
            for t in range(1, n):
                a, b = (c3 * t) % n, (c1 * t) % n
                if window_ok(a, b, n):
                    found_window = (t, a, b)
                x, y = balanced(a, n), balanced(b, n)
                if (x, y) != (0, 0) and abs(x) <= abs(i) and abs(y) <= abs(j) \
                   and not (abs(x) == abs(i) and abs(y) == abs(j)):
                    found_min = (t, x, y)
            if found_window is None and found_min is None:
                bad.append((c3, c1))
            elif verbose:
                print(f"  (c3,c1)=({c3},{c1}): window={found_window} min_viol={found_min}")
    return bad

print("== Unresolved special triples ==")
for (i, j, n) in [(4, 2, 8), (4, 2, 14), (4, -2, 8)]:
    bad = check(i, j, n, verbose=True)
    print(f"(i,j,n)=({i},{j},{n}): generator pairs with NO resolution: {bad}")
    print()

print("== Fibre cases (i,0), i | n: does full group always contain a window element? ==")
for i in (2, 3, 4):
    worst = []
    for n in range(7, 200):
        if n % i != 0:
            continue
        bad = check(i, 0, n)
        if bad:
            worst.append((n, bad))
    print(f"(i,j)=({i},0), i|n, n in [7,200): unresolved generator pairs: {worst if worst else 'NONE'}")
