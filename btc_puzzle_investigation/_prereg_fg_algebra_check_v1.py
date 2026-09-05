#!/usr/bin/env python3
"""EXACT (int-only) verification of the algebraic facts asserted in the prereg.
No float anywhere. Curve E: y^2 = x^3 + 7 over F_p, prime order n."""
import sys
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from t_y_maxbound_v1 import prime_order_curve, group_coords

def glv_beta(p):
    e = (p - 1) // 3
    g = 2
    while pow(g, e, p) == 1:
        g += 1
    return pow(g, e, p)

def check(p_lo, p_hi):
    r = prime_order_curve(p_lo, p_hi)
    if not r: return
    p, n, G = r
    xs, ys = group_coords(G, p, n, 0)
    beta = glv_beta(p)
    print(f"\n=== p={p} n={n} beta={beta}  beta^3={pow(beta,3,p)} beta^7 mod p={pow(beta,7,p)} ===")

    # (0) no 2-torsion => y_d != 0 for all d=1..n-1  (R1 always defined)
    nz = all(ys[d] % p != 0 for d in range(1, n))
    print(f"  [0] y_d != 0 for all d in 1..n-1 : {nz}")

    # (1) R2 as literally written == R1 + 3*R1^7 mod p, exactly, for every d
    ok1 = True; ok1_T = True
    R1 = [0]*n; R2lit = [0]*n; R2poly = [0]*n
    for d in range(1, n):
        x, y = xs[d] % p, ys[d] % p
        yinv = pow(y, p-2, p)
        r1 = x * yinv % p
        den = (pow(x,3,p) + 7) % p                 # == y^2
        assert den == y*y % p
        lit = r1 * (1 + 3*pow(x,6,p)*pow(pow(den,3,p), p-2, p)) % p
        pol = (r1 + 3*pow(r1,7,p)) % p
        T = (-x * yinv) % p                        # T = -x/y
        litT = r1 * (1 + 3*pow(T,6,p)) % p
        R1[d], R2lit[d], R2poly[d] = r1, lit, pol
        if lit != pol: ok1 = False
        if lit != litT: ok1_T = False
    print(f"  [1] 3x^6/(x^3+7)^3 == 3T^6 (T=-x/y), all d           : {ok1_T}")
    print(f"  [2] R2 == R1 + 3*R1^7 (mod p), all d                 : {ok1}")

    # (3) fibers of R1 over the orbit: is R1 injective on d? max fiber size
    from collections import Counter
    c1 = Counter(R1[1:]); c2 = Counter(R2poly[1:])
    print(f"  [3] R1: distinct values {len(c1)}/{n-1}, max fiber {max(c1.values())}")
    print(f"      R2: distinct values {len(c2)}/{n-1}, max fiber {max(c2.values())}")

    # (4) is f(t)=t+3t^7 a bijection of F_p?  (post-processing collapse)
    img = set((t + 3*pow(t,7,p)) % p for t in range(p))
    print(f"  [4] f(t)=t+3t^7 on F_p: |image|={len(img)}/{p}  bijection={len(img)==p}")

    # (5) mu6 oddness: R(-d) = -R(d).  P_{-d} = (x_d, p-y_d)
    ok5a = all((R1[n-d] + R1[d]) % p == 0 for d in range(1, n))
    ok5b = all((R2poly[n-d] + R2poly[d]) % p == 0 for d in range(1, n))
    print(f"  [5] R1(-d) = -R1(d) all d : {ok5a};  R2(-d) = -R2(d) all d : {ok5b}")

    # (6) GLV covariance: phi(x,y)=(beta x, y) is [lam] for some lam in Z/n.
    #     Find lam: phi(G) = [lam]G. Then check R1([lam d]G)=beta*R1([d]G) and same for R2.
    lam = None
    bx, by = beta*xs[1] % p, ys[1] % p
    for d in range(1, n):
        if xs[d] == bx and ys[d] == by:
            lam = d; break
    print(f"  [6] lambda = {lam}  (lam^2+lam+1 mod n = {(lam*lam+lam+1) % n if lam else None})")
    ok6a = ok6b = True
    for d in range(1, n):
        e = lam*d % n
        if e == 0: continue
        if R1[e] != beta*R1[d] % p: ok6a = False
        if R2poly[e] != beta*R2poly[d] % p: ok6b = False
    print(f"      R1([lam d]G) == beta*R1([d]G) all d : {ok6a}")
    print(f"      R2([lam d]G) == beta*R2([d]G) all d : {ok6b}")

    # (7) the literal proposal 'R2([w d]G) == w * R2([d]G)' with w=lam in Z/n:
    #     type-check by taking w's integer representative and multiplying in F_p.
    bad = sum(1 for d in range(1, n) if R2poly[lam*d % n] != (lam % p)*R2poly[d] % p)
    print(f"  [7] literal 'R2([lam d]G) == lam * R2([d]G)' (lam as int, mult in F_p):"
          f" fails for {bad}/{n-1} d")

    # (8) sqrt(-3) mod n vs lambda
    s = None
    for t in range(1, min(n, 200000)):
        if t*t % n == (-3) % n: s = t; break
    if s is not None:
        cands = {(( -1 + s) * pow(2, n-2, n)) % n, ((-1 - s) * pow(2, n-2, n)) % n}
        print(f"  [8] sqrt(-3) mod n = {s} (and {n-s});  (-1+-s)/2 = {sorted(cands)};"
              f"  lam in that set: {lam in cands};  s == lam: {s == lam}")

for lo, hi in [(150, 250), (250, 400), (400, 550), (900, 1100)]:
    check(lo, hi)
