#!/usr/bin/env python3
"""BHK Table 9 scan: for each pair (i,j), i in {3,4}, |j| <= 2, and each n >= 7,
determine
  (a) whether some multiple m of the group element (i,j)/n lands in the
      sufficient witness window:  a = i*m mod n, b = j*m mod n,
      n <= 6a <= 5n  and  n + 3a <= 9b <= 5n + 3a;
  (b) if not, whether minimality of (i,j) is contradicted: some multiple
      m*(i,j) mod n has balanced representative (x,y) != (0,0) with
      |x| <= |i|, |y| <= |j|, not (|x|=|i| and |y|=|j|).
"""

def balanced(r, n):
    r %= n
    return r if r <= n // 2 else r - n

def witness_exists(i, j, n):
    for m in range(1, n + 1):
        a = (i * m) % n
        b = (j * m) % n
        if n <= 6 * a <= 5 * n and n + 3 * a <= 9 * b <= 5 * n + 3 * a:
            return m
    return None

def minimality_violation(i, j, n):
    for m in range(2, n):
        x = balanced(i * m, n)
        y = balanced(j * m, n)
        if (x, y) == (0, 0):
            continue
        if abs(x) <= abs(i) and abs(y) <= abs(j) and not (abs(x) == abs(i) and abs(y) == abs(j)):
            return (m, x, y)
    return None

NMAX = 300
for i in (3, 4):
    for j in (-2, -1, 0, 1, 2):
        gaps = []
        for n in range(7, NMAX + 1):
            if witness_exists(i, j, n) is None:
                mv = minimality_violation(i, j, n)
                gaps.append((n, mv))
        unresolved = [(n, mv) for (n, mv) in gaps if mv is None]
        gap_ns = [n for (n, _) in gaps]
        print(f"(i,j)=({i},{j:+d}): #gaps in [7,{NMAX}] = {len(gap_ns)}")
        if len(gap_ns) <= 40:
            for (n, mv) in gaps:
                print(f"    n={n}: minimality violation = {mv}")
        else:
            print(f"    gap n's: {gap_ns[:30]} ... (first 30)")
            bad = [n for (n, mv) in gaps if mv is None]
            print(f"    gaps with NO minimality violation: {bad[:30]}{'...' if len(bad)>30 else ''}")
        if unresolved and len(gap_ns) > 40:
            pass
        elif unresolved:
            print(f"    *** UNRESOLVED: {[n for n,_ in unresolved]}")
