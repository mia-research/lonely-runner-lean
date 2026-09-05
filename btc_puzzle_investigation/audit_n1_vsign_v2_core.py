#!/usr/bin/env python3
"""audit_n1_vsign_v2_core.py -- independent exact recomputation for the audit of
PREREG_n1_v_sign_sweep_v2.md.  EXACT INTEGER ARITHMETIC ONLY in the signal path.

Object: E : y^2 = x^3 + 7 over F_p (j=0), #E(F_p) = n prime.
  V_k(a) = sum_{P in E(F_{p^k})} chi2^{(k)}(y_P) * zeta_n^{ a * dlog(Tr_{k/1} P) }
  P_k(a) = -V_k(a)   (Lefschetz)
  e2(a)  = (P_1^2 - P_2)/2 = (V_1(a)^2 + V_2(a))/2      [F1]
All of V_1, V_2, e2 are handled as integer polynomials mod (x^n - 1) / Phi_n(x);
no float ever enters.
"""
import sys
from fractions import Fraction

# ---------------- basic number theory (exact) ----------------
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

def curve_order(p, B=7):
    """#E(F_p) for y^2 = x^3 + B, exact integer count."""
    n = p+1
    for x in range(p):
        n += legendre((x*x % p * x + B) % p, p)
    return n

# ---------------- E(F_p) group law ----------------
def ec_add(P, Q, p, B=7):
    if P is None: return Q
    if Q is None: return P
    x1,y1 = P; x2,y2 = Q
    if x1 == x2 and (y1+y2) % p == 0: return None
    if P == Q:
        lam = (3*x1*x1 % p) * pow(2*y1 % p, p-2, p) % p
    else:
        lam = (y2-y1) * pow((x2-x1) % p, p-2, p) % p
    x3 = (lam*lam - x1 - x2) % p
    y3 = (lam*(x1-x3) - y1) % p
    return (x3,y3)

def find_generator(p, n, B=7):
    for x in range(p):
        r = (x*x % p * x + B) % p
        if legendre(r,p) == 1:
            y = tonelli(r,p)
            return (x,y)
    raise RuntimeError

def tonelli(a,p):
    a %= p
    if p % 4 == 3: return pow(a,(p+1)//4,p)
    # general Tonelli-Shanks
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

def dlog_table(p, n, B=7):
    G = find_generator(p,n,B)
    dl = {}
    Q = None; d = 0
    while d < n:
        dl[Q] = d
        Q = ec_add(Q,G,p,B); d += 1
    return dl

# ---------------- F_{p^2} ----------------
class F2:
    """F_{p^2} = F_p[t]/(t^2 - s), s a fixed non-residue.  Elements = (a,b)."""
    def __init__(self,p):
        self.p = p
        s = 2
        while legendre(s,p) != -1: s += 1
        self.s = s
    def mul(self,u,v):
        p,s = self.p,self.s
        a,b = u; c,d = v
        return ((a*c + s*b*d) % p, (a*d + b*c) % p)
    def sq(self,u): return self.mul(u,u)
    def pw(self,u,e):
        r = (1,0)
        while e:
            if e & 1: r = self.mul(r,u)
            u = self.mul(u,u); e >>= 1
        return r
    def add(self,u,v):
        p = self.p
        return ((u[0]+v[0]) % p, (u[1]+v[1]) % p)
    def sub(self,u,v):
        p = self.p
        return ((u[0]-v[0]) % p, (u[1]-v[1]) % p)
    def neg(self,u):
        p = self.p
        return ((-u[0]) % p, (-u[1]) % p)
    def inv(self,u):
        p,s = self.p,self.s
        a,b = u
        d = (a*a - s*b*b) % p
        di = pow(d,p-2,p)
        return (a*di % p, (-b)*di % p)
    def frob(self,u):   # (a+bt)^p = a - bt   since s^((p-1)/2) = -1
        return (u[0], (-u[1]) % self.p)

def ec_add2(F,P,Q,B=7):
    if P is None: return Q
    if Q is None: return P
    x1,y1 = P; x2,y2 = Q
    if x1 == x2 and F.add(y1,y2) == (0,0): return None
    if P == Q:
        num = F.mul((3,0), F.sq(x1)); den = F.mul((2,0), y1)
    else:
        num = F.sub(y2,y1); den = F.sub(x2,x1)
    lam = F.mul(num, F.inv(den))
    x3 = F.sub(F.sub(F.sq(lam), x1), x2)
    y3 = F.sub(F.mul(lam, F.sub(x1,x3)), y1)
    return (x3,y3)

# ---------------- histograms (exact integers) ----------------
def hist_k1(p, n, dl, B=7):
    h = [0]*n
    half = (p-1)//2
    for x in range(p):
        r = (x*x % p * x + B) % p
        if r == 0: continue
        if legendre(r,p) != 1: continue
        y = tonelli(r,p)
        for yy in (y, (-y) % p):
            c = 1 if pow(yy, half, p) == 1 else -1
            h[dl[(x,yy)]] += c
    return h

def hist_k2(p, n, dl, B=7):
    """h2[d] = sum over P in E(F_{p^2}) with Tr(P)=[d]G of chi2^{(2)}(y_P)."""
    F = F2(p)
    q = p*p
    half = (q-1)//2
    # table of squares in F_{p^2}
    sqrt_tab = {}
    for a in range(p):
        for b in range(p):
            z = (a,b)
            sqrt_tab[F.sq(z)] = z
    h = [0]*n
    Bq = (B % p, 0)
    for a in range(p):
        for b in range(p):
            x = (a,b)
            r = F.add(F.mul(F.sq(x), x), Bq)
            if r == (0,0): continue
            y = sqrt_tab.get(r)
            if y is None: continue          # non-square
            for yy in (y, F.neg(y)):
                c = 1 if F.pw(yy, half) == (1,0) else -1
                P = (x,yy)
                T = ec_add2(F, P, (F.frob(x), F.frob(yy)), B)
                if T is None:
                    d = 0
                else:
                    assert T[0][1] == 0 and T[1][1] == 0, "trace not in E(F_p)"
                    d = dl[(T[0][0], T[1][0])]
                h[d] += c
    return h

# ---------------- Z[x]/(x^n-1) and Phi_n ----------------
def polymul_mod_cyc(A,B,n):
    C = [0]*n
    for i,ai in enumerate(A):
        if ai == 0: continue
        for j,bj in enumerate(B):
            if bj == 0: continue
            C[(i+j) % n] += ai*bj
    return C

def reduce_phi_prime(A,n):
    """reduce mod Phi_n = 1+x+...+x^{n-1} (n prime): subtract A[n-1]*(all ones)."""
    c = A[n-1]
    return [A[i]-c for i in range(n-1)]

def sigma(A, c, n):
    """Galois action zeta -> zeta^c on a vector in Z[x]/(x^n-1)."""
    out = [0]*n
    for i,ai in enumerate(A):
        out[(i*c) % n] += ai
    return out

def compute_e2_poly(p, B=7, verbose=True):
    n = curve_order(p,B)
    assert is_prime(n), (p,n)
    dl = dlog_table(p,n,B)
    h1 = hist_k1(p,n,dl,B)
    h2 = hist_k2(p,n,dl,B)
    A2 = polymul_mod_cyc(h1,h1,n)
    W = [A2[i] + h2[i] for i in range(n)]   # W = V1^2 + V2 as poly ; e2 = W/2
    return n, h1, h2, W

if __name__ == "__main__":
    for p in (13,43):
        n,h1,h2,W = compute_e2_poly(p)
        print(f"p={p} n={n} (n-1)/6={(n-1)//6}")
        print("  h1 =",h1)
        print("  h2 =",h2)
        print("  sum h1 =",sum(h1)," sum h2 =",sum(h2))
        print("  W = V1^2+V2 coeffs (mod x^n-1):",W)
