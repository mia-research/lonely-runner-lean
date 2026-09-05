#!/usr/bin/env python3
"""
core2 windowed-pentagon de-risk (2026-06-23)
=============================================
Question for brick 6: in the *core2* regime v1 < 1/6 (i.e. 6p < q), do the three
pentagon branches ((1,1) diagonal, (1,2), (1,-2)) admit a witness in the SMALLER
pentagon P' = P ∩ {Y <= 5/12 - v1/3}  (BHK condition (43), v1/3 = p/(3q))?

C-point at half-integer index l:  m = 2l+1 (odd),
   X = frac(r*m/(2q)),  Y = frac(p*m/(2q)).
P (reduced coords, g cancels; p2 = q-p = w1/g, s = w4/g = v5*q):
   X >= 1/6 - r*(s-q)/(3*q*s)
   Y >= 1/6 - p*(s-q)/(3*q*s)
   Y <= 1/3 + p2*(s-q)/(3*q*s)
   X <= 5/6
   1/(3s) <= (5/6 - X)/r + (Y - 1/6)/p
   1/(3s) <= (5/6 - X)/r + (1/3 - Y)/p2
P' adds:
   Y <= 5/12 - p/(3q)

Rigidity per branch (relation j*r ≡ i*p mod q, r in (q, 3q/2)):
   (1,1):   r = p + q              (diagonal)
   (1,2):   2r = 2q + p            (=> p even)
   (1,-2):  2r + p = 3q            (=> p,q odd, etc.)

For each (q,p,r) we sweep completions s in (r, 3q] (p2 = q-p fixed) and ask:
exists odd m in [1, 2q) with C-point in P'?  Report failures (no witness).

RESULT (2026-06-23):
  (1,2):  0 P'-witness failures (all completions) -> windowed kill TRACTABLE
  (1,-2): 0 P'-witness failures (all completions) -> windowed kill TRACTABLE
  (1,1):  734 failures at q>=18  -> the diagonal CANNOT use a pentagon witness.
          This is exactly why BHK gives the diagonal its own Part-6 (Claims
          19-21, gap at t = x1(k+1/6)), NOT the pentagon. So core2's (1,1)
          branch needs the WINDOWED Part 6 (fictional 0123-gap), not pent_no_good2.
"""
import math

def frac(x):
    return x - math.floor(x)

def in_Pprime(X, Y, p, q, r, p2, s):
    M = (s - q) / (3.0 * q * s)
    eps = 1e-12
    if X < 1/6 - r*M - eps: return False
    if Y < 1/6 - p*M - eps: return False
    if Y > 1/3 + p2*M + eps: return False
    if X > 5/6 + eps: return False
    if 1/(3*s) > (5/6 - X)/r + (Y - 1/6)/p + eps: return False
    if 1/(3*s) > (5/6 - X)/r + (1/3 - Y)/p2 + eps: return False
    # (43) cut
    if Y > 5/12 - p/(3.0*q) + eps: return False
    return True

def witness_exists(p, q, r, s):
    p2 = q - p
    for m in range(1, 2*q, 2):  # odd m = 2l+1
        X = frac(r*m/(2.0*q))
        Y = frac(p*m/(2.0*q))
        if in_Pprime(X, Y, p, q, r, p2, s):
            return m
    return None

def branch_r(branch, p, q):
    """Return r (int) for the branch, or None if relation has no valid r in (q,3q/2)."""
    if branch == "(1,1)":
        r = p + q
    elif branch == "(1,2)":
        # 2r = 2q + p  => need p even
        if p % 2 != 0: return None
        r = q + p//2
    elif branch == "(1,-2)":
        # 2r + p = 3q => 2r = 3q - p
        if (3*q - p) % 2 != 0: return None
        r = (3*q - p)//2
    else:
        return None
    if not (q < r and 2*r < 3*q):
        return None
    return r

def run(branch, qmax=72):
    total = 0
    fails = []
    min_wit = 99
    for q in range(7, qmax+1):
        for p in range(1, q):
            if math.gcd(p, q) != 1: continue
            if 6*p >= q: continue           # core2 regime v1 < 1/6
            r = branch_r(branch, p, q)
            if r is None: continue
            if math.gcd(r, q) != 1: continue
            # sweep completions s in (r, 3q]
            any_s = False
            for s in range(r+1, 3*q+1):
                total += 1
                any_s = True
                m = witness_exists(p, q, r, s)
                if m is None:
                    fails.append((q, p, r, s))
                else:
                    min_wit = min(min_wit, 1)
            # (any_s just guards empty completion ranges)
    return total, fails

for branch in ["(1,1)", "(1,2)", "(1,-2)"]:
    total, fails = run(branch)
    print(f"branch {branch:7s}: completions tested={total:6d}  P'-witness failures={len(fails)}")
    if fails:
        # show the distribution of failures by (q,p,r)
        from collections import Counter
        byqpr = Counter((q,p,r) for (q,p,r,s) in fails)
        print(f"   distinct (q,p,r) with >=1 failing s: {len(byqpr)}")
        for (q,p,r), c in sorted(byqpr.items())[:12]:
            ss = sorted(s for (qq,pp,rr,s) in fails if (qq,pp,rr)==(q,p,r))
            print(f"     q={q} p={p} r={r}: {c} failing s (e.g. {ss[:6]})")
