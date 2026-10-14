r"""
nonrep_averaging_v1  --  the two ingredients of the Dilation Theorem and of the
fibre-averaging bound, both checked exactly.

(D1) SHIFT IDENTITY.   bad(rho, t + rho*i) = bad(rho, t) - i   (mod 8), all rho,t,i.

(D2) DILATION THEOREM. For lambda odd and any base tuple E_non,
        S(lambda * E_non) = { x : lambda*x mod 1  in  S(E_non) }.
     Proof: writing lambda*x = x' + i with x' = frac(lambda x), for a speed lambda*e
     we get floor(lambda*e*x) = e*i + floor(e*x'), so t = rho*i + t_e(x') mod 8, and
     bad(lambda*rho, t) = lambda * bad(rho, rho*i + t_e(x'))   [scaling rule S1]
                        = lambda * (bad(rho, t_e(x')) - i)     [D1].
     Union over e: cov_{lambda E}(x) = lambda*(cov_E(x') - i), a bijective image, so
     it is all of Z/8 iff cov_E(x') is.

(A1) POINT COUNT.  An OPEN arc of length 1/4 in R/Z contains at most floor(L/4)+1 of
     the L points of any coset of (1/L)Z.

(A2) beta(L) := (floor(L/4)+1)/L  satisfies  beta(L) <= 2/5 for every ODD L >= 3,
     with equality only at L = 5.  (beta(L) <= 1/4 + 1/L <= 1/4+1/7 < 2/5 for L >= 7;
     beta(3) = 1/3, beta(5) = 2/5.)
"""
from fractions import Fraction as F
from math import lcm, gcd
import itertools, sys
from nonrep_sweep_v2 import safe_num_den
from nonrep_sweep_v1 import windows

BAD = {(rho, t): frozenset(r for r in range(8) if (rho * r + t) % 8 in (0, 7))
       for rho in range(1, 8) for t in range(8)}

# ---- D1
ok = all(BAD[(rho, (t + rho * i) % 8)] == frozenset((a - i) % 8 for a in BAD[(rho, t)])
         for rho in range(1, 8) for t in range(8) for i in range(8))
print(f"[D1] bad(rho, t+rho*i) == bad(rho,t) - i   for all rho,t,i in Z/8 : {'OK' if ok else 'FAIL'}")

# ---- D2 on concrete tuples: compare windows of S(lam*E) with lam^{-1}-pullback of S(E)
def pullback(wins, lam):
    out = []
    for i in range(lam):
        for a, b in wins:
            out.append([(a + i) / lam, (b + i) / lam])
    return norm(out)

def norm(ivs):
    """canonical form of a subset of R/Z given as half-open intervals: sort, merge
    touching/overlapping, then merge across the 0~1 wrap."""
    ivs = sorted([list(v) for v in ivs])
    out = []
    for a, b in ivs:
        if out and a <= out[-1][1]: out[-1][1] = max(out[-1][1], b)
        else: out.append([a, b])
    if len(out) > 1 and out[0][0] == 0 and out[-1][1] == 1:
        out[0][0] = out[-1][0] - 1; out.pop()
    return [tuple(v) for v in out]

print("\n[D2] dilation theorem on concrete base tuples (wrap-aware comparison):")
bases = [(1,3,5,7,4), (1,3,5,7,2), (9,11,5,7,4), (1,11,21,31,10), (17,3,21,23,6),
         (1,3,5,7,6), (25,3,13,7,20), (1,19,5,7,26)]
for E in bases:
    rhos = tuple(e % 8 for e in E)
    w0 = norm(windows(E, rhos))
    res = []
    for lam in (3, 5, 7, 9, 11, 13):
        E2 = tuple(lam * e for e in E)
        w2 = norm(windows(E2, tuple(e % 8 for e in E2)))
        res.append((lam, w2 == pullback(w0, lam)))
    print(f"   E={E}: " + "  ".join(f"lam={l}:{'OK' if k else 'FAIL'}" for l, k in res))

# ---- A1: point count, verified by brute force over cosets with exact rationals
print("\n[A1] open arc (-1/8,1/8) vs a coset {(c+j)/L} of (1/L)Z, worst case over c:")
worst_ok = True
for L in range(1, 41):
    mx = 0
    # the count changes only at c where some (c+j)/L hits +-1/8 ; sample all
    # critical c and midpoints, exactly
    crit = set()
    for j in range(L):
        for s in (F(1,8), F(-1,8)):
            crit.add((s * L - j) % L)
    cs = sorted(crit) or [F(0)]
    probes = list(cs) + [(cs[i] + cs[(i+1) % len(cs)]) / 2 for i in range(len(cs) - 1)]
    for c in probes:
        n = sum(1 for j in range(L) if abs(((F(c + j, L) + F(1,2)) % 1) - F(1,2)) < F(1,8))
        mx = max(mx, n)
    bound = L // 4 + 1
    if mx > bound: worst_ok = False
    if L <= 16 or L in (21,25,33,39):
        print(f"   L={L:>2}: max points in the open arc = {mx}, bound floor(L/4)+1 = {bound}"
              f"  beta = {F(bound,L)} = {float(F(bound,L)):.4f}"
              f"{'   <-- ODD' if L%2 else ''}")
print(f"   A1 holds for all L <= 40 : {'OK' if worst_ok else 'FAIL'}")

# ---- A2
bad2 = [L for L in range(3, 20001, 2) if F(L // 4 + 1, L) > F(2, 5)]
print(f"\n[A2] odd L in [3,20000] with beta(L) > 2/5 : {bad2}   "
      f"(analytic: beta(L) <= 1/4 + 1/L <= 11/28 < 2/5 for L >= 7; beta(3)=1/3, beta(5)=2/5)")
print(f"     max beta over odd L >= 3 = {max(F(L//4+1,L) for L in range(3,2001,2))}")
