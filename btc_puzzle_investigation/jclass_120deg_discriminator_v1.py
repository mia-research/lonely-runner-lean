#!/usr/bin/env python3
"""jclass_120deg_discriminator_v1.py -- instrument for PREREG_jclass_120deg_discriminator (v2 pending).

Generalizes the record's 120-degree census machinery from y^2 = x^3 + B (j=0 only) to
y^2 = x^3 + A x + B (any j), so that the SAME statistic can be evaluated across curve classes.

EXACT INTEGER / MODULAR ARITHMETIC ONLY.  No float anywhere in the signal path.

Statistic (unchanged from run_n1_120deg_v1.py):
    g_k(p,A,B,a) = deg gcd( L*(T), L*(zeta_k T) )
with L* rebuilt from V1,V2 by the forced-coefficient rule
    e1 = -V1 ,  e2 = (V1^2 + V2)/2 ,  e3 = chi2(-1)*p*e1 ,  e4 = p^2
which depends only on purity + the alpha |-> -conj(alpha) closure + p mod 4 -- NOT on j.

MODES
  --check   plants + reproduction of the published j=0 numbers.  Runs no arm.  (pre-gate legal)
  --arms    the actual discriminator.  GATED: refuses to run without --i-have-the-gate.
"""
import sys, json, time

# ----------------------------------------------------------------- basic arithmetic
def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def legendre(a,p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a,(p-1)//2,p) == 1 else -1

def tonelli(a,p):
    a %= p
    if p % 4 == 3: return pow(a,(p+1)//4,p)
    s = p-1; e = 0
    while s % 2 == 0: s//=2; e+=1
    nq = 2
    while legendre(nq,p) != -1: nq += 1
    x = pow(a,(s+1)//2,p); b = pow(a,s,p); g = pow(nq,s,p); r = e
    while True:
        t = b; m = 0
        while t != 1:
            t = t*t % p; m += 1
        if m == 0: return x
        gs = pow(g, 1 << (r-m-1), p)
        g = gs*gs % p; x = x*gs % p; b = b*g % p; r = m

def prime_factors(m):
    fs = set(); d = 2
    while d*d <= m:
        while m % d == 0: fs.add(d); m //= d
        d += 1
    if m > 1: fs.add(m)
    return fs

def root_of_order(k, l):
    """element of F_l of order EXACTLY k.  (D5: the predecessor's version assumed k prime.)"""
    assert (l-1) % k == 0, (k,l)
    qs = prime_factors(k)
    b = 2
    while b < l:
        z = pow(b, (l-1)//k, l)
        if z != 1 and all(pow(z, k//q, l) != 1 for q in qs):
            assert pow(z, k, l) == 1
            return z
        b += 1
    raise RuntimeError("no element of order %d in F_%d" % (k,l))

# ----------------------------------------------------------------- curve y^2 = x^3 + Ax + B
def rhs(x, p, A, B):  return (x*x % p * x + A*x + B) % p

def discriminant_nonzero(p, A, B):  return (4*A%p*A%p*A + 27*B%p*B) % p != 0

def j_class(A, B):
    if A == 0: return "j0"
    if B == 0: return "j1728"
    return "jgen"

def curve_order(p, A, B):
    n = p+1
    for x in range(p): n += legendre(rhs(x,p,A,B), p)
    return n

def ec_add(P, Q, p, A):
    if P is None: return Q
    if Q is None: return P
    x1,y1 = P; x2,y2 = Q
    if x1 == x2 and (y1+y2) % p == 0: return None
    if P == Q:
        lam = (3*x1*x1 + A) % p * pow(2*y1 % p, p-2, p) % p
    else:
        lam = (y2-y1) * pow((x2-x1) % p, p-2, p) % p
    x3 = (lam*lam - x1 - x2) % p
    y3 = (lam*(x1-x3) - y1) % p
    return (x3,y3)

def find_generator(p, A, B):
    for x in range(p):
        r = rhs(x,p,A,B)
        if legendre(r,p) == 1:
            return (x, tonelli(r,p))
    raise RuntimeError

def dlog_table(p, n, A, B):
    G = find_generator(p,A,B)
    dl = {}; Q = None; d = 0
    while d < n:
        dl[Q] = d; Q = ec_add(Q,G,p,A); d += 1
    assert Q is None, "generator did not have order n"
    return dl

class F2:
    """F_{p^2} = F_p[t]/(t^2 - s), s a fixed non-residue."""
    def __init__(self,p):
        self.p = p; s = 2
        while legendre(s,p) != -1: s += 1
        self.s = s
    def mul(self,u,v):
        p,s = self.p,self.s; a,b = u; c,d = v
        return ((a*c + s*b*d) % p, (a*d + b*c) % p)
    def sq(self,u): return self.mul(u,u)
    def pw(self,u,e):
        r = (1,0)
        while e:
            if e & 1: r = self.mul(r,u)
            u = self.mul(u,u); e >>= 1
        return r
    def add(self,u,v):
        p = self.p; return ((u[0]+v[0])%p, (u[1]+v[1])%p)
    def sub(self,u,v):
        p = self.p; return ((u[0]-v[0])%p, (u[1]-v[1])%p)
    def neg(self,u):
        p = self.p; return ((-u[0])%p, (-u[1])%p)
    def inv(self,u):
        p,s = self.p,self.s; a,b = u
        di = pow((a*a - s*b*b) % p, p-2, p)
        return (a*di % p, (-b)*di % p)
    def frob(self,u): return (u[0], (-u[1]) % self.p)

def ec_add2(F,P,Q,A):
    if P is None: return Q
    if Q is None: return P
    x1,y1 = P; x2,y2 = Q
    if x1 == x2 and F.add(y1,y2) == (0,0): return None
    if P == Q:
        num = F.add(F.mul((3,0), F.sq(x1)), (A % F.p, 0)); den = F.mul((2,0), y1)
    else:
        num = F.sub(y2,y1); den = F.sub(x2,x1)
    lam = F.mul(num, F.inv(den))
    x3 = F.sub(F.sub(F.sq(lam), x1), x2)
    return (x3, F.sub(F.mul(lam, F.sub(x1,x3)), y1))

def hist_k1(p, n, dl, A, B):
    h = [0]*n; half = (p-1)//2
    for x in range(p):
        r = rhs(x,p,A,B)
        if r == 0 or legendre(r,p) != 1: continue
        y = tonelli(r,p)
        for yy in (y, (-y) % p):
            h[dl[(x,yy)]] += 1 if pow(yy, half, p) == 1 else -1
    return h

def hist_k2(p, n, dl, A, B):
    F = F2(p); q = p*p; half = (q-1)//2
    sqrt_tab = {}
    for a in range(p):
        for b in range(p): sqrt_tab[F.sq((a,b))] = (a,b)
    h = [0]*n; Aq = (A % p, 0); Bq = (B % p, 0)
    for a in range(p):
        for b in range(p):
            x = (a,b)
            r = F.add(F.add(F.mul(F.sq(x), x), F.mul(Aq, x)), Bq)
            if r == (0,0): continue
            y = sqrt_tab.get(r)
            if y is None: continue
            for yy in (y, F.neg(y)):
                c = 1 if F.pw(yy, half) == (1,0) else -1
                T = ec_add2(F, (x,yy), (F.frob(x), F.frob(yy)), A)
                if T is None: d = 0
                else:
                    assert T[0][1] == 0 and T[1][1] == 0, "trace not in E(F_p)"
                    d = dl[(T[0][0], T[1][0])]
                h[d] += c
    return h

# ----------------------------------------------------------------- exact poly gcd over F_l
def _norm(Apoly, l):
    Apoly = [c % l for c in Apoly]
    while Apoly and Apoly[-1] == 0: Apoly.pop()
    return Apoly

def _rem(Apoly, Bpoly, l):
    Apoly = _norm(Apoly, l); Bpoly = _norm(Bpoly, l)
    inv = pow(Bpoly[-1], l-2, l)
    while len(Apoly) >= len(Bpoly):
        f = Apoly[-1]*inv % l; sh = len(Apoly)-len(Bpoly)
        for i in range(len(Bpoly)): Apoly[sh+i] = (Apoly[sh+i]-f*Bpoly[i]) % l
        Apoly = _norm(Apoly, l)
        if not Apoly: break
    return Apoly

def deg_gcd(Apoly, Bpoly, l):
    Apoly = _norm(Apoly[:], l); Bpoly = _norm(Bpoly[:], l)
    while Bpoly: Apoly, Bpoly = Bpoly, _rem(Apoly, Bpoly, l)
    return (len(Apoly)-1) if Apoly else -1

def ell_primes(n, count=5, modulus_extra=12):
    """first `count` primes l == 1 mod (modulus_extra * n): gives zeta_n and zeta_k for k | 12."""
    step = modulus_extra*n; l = step + 1; out = []
    while len(out) < count:
        if is_prime(l): out.append(l)
        l += step
    return out

# ----------------------------------------------------------------- the statistic
def g_flags(p, n, h1, h2, a, ells, ks=(3,4,6)):
    """returns (dict k->g_k, V1_is_zero, has_repeated_root), min over ell."""
    gmin = {k: 4 for k in ks}; zero_all = True; rep_min = 4
    for l in ells:
        r = root_of_order(n, l)
        inv2 = pow(2, l-2, l)
        ra = pow(r, a % n, l)
        rp = 1; V1 = 0; V2 = 0
        for d in range(n):
            if h1[d]: V1 = (V1 + h1[d]*rp) % l
            if h2[d]: V2 = (V2 + h2[d]*rp) % l
            rp = rp*ra % l
        if V1 != 0: zero_all = False
        e1 = (-V1) % l
        e2 = (V1*V1 + V2)*inv2 % l
        leg = 1 if p % 4 == 1 else -1                 # chi2(-1)
        e3 = (leg*p*e1) % l
        e4 = (p*p) % l
        L  = [e4, (-e3) % l, e2, (-e1) % l, 1]        # low -> high
        for k in ks:
            z = root_of_order(k, l)
            zk = [pow(z, idx, l) for idx in range(5)]
            Lz = [L[idx]*zk[idx] % l for idx in range(5)]
            gmin[k] = min(gmin[k], deg_gcd(L, Lz, l))
        Ld = [L[1], 2*L[2] % l, 3*L[3] % l, 4*L[4] % l]
        rep_min = min(rep_min, deg_gcd(L, Ld, l))
    return gmin, zero_all, (rep_min > 0)

def cube_root_of_unity(n):
    rt = tonelli((-3) % n, n); inv2 = pow(2, n-2, n)
    c1 = (-1 + rt) * inv2 % n; c2 = (-1 - rt) * inv2 % n
    assert (c1*c1+c1+1) % n == 0 and (c2*c2+c2+1) % n == 0
    return min(c1, c2)

def cells(n, has_mu3):
    """mu_6 cosets when the curve has the mu_3 twist symmetry, else mu_2 cosets."""
    if has_mu3:
        z3 = cube_root_of_unity(n); z3sq = z3*z3 % n
        U = [1 % n, (n-1) % n, z3, (n-z3) % n, z3sq, (n-z3sq) % n]
    else:
        U = [1 % n, (n-1) % n]
    seen = bytearray(n); reps = []
    for m in range(1, n):
        if seen[m]: continue
        reps.append(m)
        for u in U: seen[m*u % n] = 1
    assert len(reps) == (n-1)//len(U), (len(reps), n, len(U))
    return reps

# ----------------------------------------------------------------- CONTROLS
def plant_check(ks=(3,4,6)):
    """C-PLANT: synthetic quartics with planted ratios, through the SAME deg_gcd routine."""
    l = 13
    while not (is_prime(l) and (l-1) % 24 == 0): l += 1     # need i and zeta_k for k|12
    i0 = tonelli((l-1) % l, l)
    res = {}; ok = True
    def poly_from_roots(rs):
        P = [1]
        for rt in rs:
            Q = [0]*(len(P)+1)
            for idx, c in enumerate(P):
                Q[idx]   = (Q[idx]   - c*rt) % l
                Q[idx+1] = (Q[idx+1] + c) % l
            P = Q
        return P
    def gof(P, k):
        z = root_of_order(k, l)
        zk = [pow(z, idx, l) for idx in range(len(P))]
        return deg_gcd(P, [P[idx]*zk[idx] % l for idx in range(len(P))], l)
    # POSITIVE plants use a prime-norm Weil number (norm 13).
    alpha = (3 + 2*i0) % l; ca = (3 - 2*i0) % l
    # NEGATIVE plant: two Weil numbers of the SAME norm that are NOT associates.
    #   The predecessor (run_n1_120deg_v1.py:143-144) used alpha=3+2i, beta=2+3i, both of PRIME
    #   norm 13 -- but Z[i] has unique factorisation, so any two elements of a prime norm are
    #   related by a unit times conjugation: beta = i*conj(alpha) EXACTLY.  That plant therefore
    #   carries a zeta_4 ratio by construction and is not a generic negative control.  It reports
    #   g_3 = 0 correctly, so no published k=3 number is affected -- but it cannot be reused at
    #   k = 4.  A composite norm is required.  norm 65 = 5*13:
    #        gA = (2+i)(3+2i) = 4+7i ,   gB = (2+i)(3-2i) = 8-i        (both norm 65)
    gA = (4 + 7*i0) % l; cA = (4 - 7*i0) % l
    gB = (8 - 1*i0) % l; cB = (8 + 1*i0) % l
    # SELF-VALIDATION: the negative plant must carry NO root-of-unity ratio of order <= 12.
    neg_roots = [gA, gB, (-cA) % l, (-cB) % l]
    bad = []
    for u in neg_roots:
        for v in neg_roots:
            if u == v: continue
            ratio = u * pow(v, l-2, l) % l
            for kk in range(2, 13):
                if pow(ratio, kk, l) == 1: bad.append((kk, u, v)); break
    if bad:
        print("    *** negative plant is NOT lock-free: ratios of order", sorted({b[0] for b in bad}))
        ok = False
    else:
        res["PLANT-N lock-free (orders<=12)"] = "verified"
    for k in ks:
        z  = root_of_order(k, l); zbar = pow(z, k-1, l)
        # PLANT-k: {alpha, z*alpha, -conj alpha, -zbar*conj alpha}  -> want g_k = 2
        Pk = poly_from_roots([alpha, z*alpha % l, (-ca) % l, (-zbar*ca) % l])
        # PLANT-N: {gA, gB, -conj gA, -conj gB}, verified lock-free -> want g_k = 0
        Pn = poly_from_roots(neg_roots)
        gk, gn = gof(Pk, k), gof(Pn, k)
        res["PLANT-%d(want2)" % k] = gk
        res["PLANT-N%d(want0)" % k] = gn
        ok = ok and gk == 2 and gn == 0
        # cross-check: a zeta_k plant must NOT register at a different order k'
        for k2 in ks:
            if k2 == k: continue
            res["PLANT-%d @g_%d(want0)" % (k,k2)] = gof(Pk, k2)
            ok = ok and gof(Pk, k2) == 0
    print("C-PLANT over F_%d:" % l)
    for kk in sorted(res): print("    %-24s = %s" % (kk, res[kk]))
    print("    ->", "ALL FIRE" if ok else "*** FAIL ***")
    return ok

def order_check():
    """C-ORDER: root_of_order returns EXACT order, incl. composite k (D5)."""
    ok = True
    for l in (73, 97, 193, 241, 337):
        if not is_prime(l): continue
        for k in (3,4,6,12):
            if (l-1) % k: continue
            z = root_of_order(k, l)
            true_order = 1; t = z
            while t != 1: t = t*z % l; true_order += 1
            if true_order != k:
                print("    *** F_%d k=%d -> order %d" % (l,k,true_order)); ok = False
    print("C-ORDER: root_of_order exact for k in {3,4,6,12} over 5 primes ->",
          "PASS" if ok else "*** FAIL ***")
    return ok

def repro_check(primes=(43,67,79,127)):
    """C-REPRO: the generalized pipeline must reproduce the published j=0 census cell-for-cell."""
    try:
        pub = json.load(open("RESULT_n1_120deg_exact_v1.json"))
    except FileNotFoundError:
        print("C-REPRO: published JSON missing -> CANNOT CHECK"); return False
    idx = {r["p"]: r for grp in ("IN","S","C") for r in pub.get(grp, []) if r}
    ok = True
    for p in primes:
        if p not in idx:
            print("    p=%d not in published set, skipping" % p); continue
        want = idx[p]
        n = curve_order(p, 0, 7)
        assert is_prime(n), (p, n)
        dl = dlog_table(p, n, 0, 7)
        h1 = hist_k1(p, n, dl, 0, 7); h2 = hist_k2(p, n, dl, 0, 7)
        ells = ell_primes(n, 5)
        reps = cells(n, has_mu3=True)
        dist = {}; zero = 0; rep = 0
        for a in reps:
            g, is0, isrep = g_flags(p, n, h1, h2, a, ells, ks=(3,))
            if is0: zero += 1; continue
            if isrep: rep += 1; continue
            dist[g[3]] = dist.get(g[3], 0) + 1
        got = {"dist": {str(k): v for k,v in dist.items()}, "zero": zero, "rep": rep,
               "cells": len(reps)}
        exp = {"dist": {str(k): v for k,v in want["dist"].items()}, "zero": want["zero"],
               "rep": want["rep"], "cells": want["cells"]}
        match = got == exp
        ok = ok and match
        print("    p=%-5d got %s" % (p, got))
        print("           pub %s   -> %s" % (exp, "MATCH" if match else "*** MISMATCH ***"))
    print("C-REPRO ->", "PASS" if ok else "*** FAIL ***")
    return ok

if __name__ == "__main__":
    if "--check" in sys.argv:
        print("=" * 78)
        print("INSTRUMENT CHECKS -- no arm is run, no new curve class is touched.")
        print("=" * 78)
        a = order_check(); print()
        b = plant_check(); print()
        c = repro_check()
        print("\nOVERALL:", "READY" if (a and b and c) else "*** NOT READY ***")
        sys.exit(0 if (a and b and c) else 1)
    if "--arms" in sys.argv:
        if "--i-have-the-gate" not in sys.argv:
            print("REFUSING: PREREG v2 is not issued and the experiment-designer gate has not "
                  "returned.\nSee PREREG_jclass_120deg_discriminator_v1_DEVIATIONS.md (D1-D5).")
            sys.exit(2)
        print("arm runner not yet written -- v2 spec must fix the prime class first (D1).")
        sys.exit(2)
    print(__doc__)
