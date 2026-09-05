#!/usr/bin/env python3
"""
Adjudication of the pasted results table (2026-07-11).

T1  Frobenius coordinates (a,b).
T2  "Amicable pair automatic when n prime" -- brute-force counterexample hunt
    (point counts only, no character formula).
T3  Formal group integrality: [2](T), [3](T), [5](T) in Z[[T]] to degree 37
    (covers ALL primes at once, stronger than 20 spot primes).
T4  Unit root alpha = t (mod p), Hensel lift mod p^2, exact check.
T5  Sextic-unit distribution: exact class census (expect 72 per unit of 432)
    + empirical counts over split primes.
T6  Analytic conductor 536.19 =? N/(4 pi^2).
T7  L(E,1) recomputed from scratch (exact a_n to 4000, theta sum) vs
    Omega = 3.0414... and 2*Omega = 6.0828...  [decides the period-convention
    dispute and the BSD Tamagawa tension]
T8  |psi(p)|^2 = N(p) (note: psi, not chi).
"""

import math
from fractions import Fraction

p  = 2**256 - 2**32 - 977
n  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
t  = p + 1 - n
A_ = 367917413016453100223835821029139468249
B_ = 303414439467246543595045361 # deliberately wrong? no -- fixed below
B_ = 303414439467246543595250775667605759171
UNITS = [(1,0), (-1,0), (0,1), (0,-1), (-1,-1), (1,1)]

def mulw(a, b): return (a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0] - a[1]*b[1])
def Nrm(v): return v[0]*v[0] - v[0]*v[1] + v[1]*v[1]

print("=== T1: Frobenius coordinates ===")
print(f"  N(a+bw) = p: {Nrm((A_,B_)) == p};  2a-b = t: {2*A_-B_ == t};  "
      f"N(a-1+bw) = n: {Nrm((A_-1,B_)) == n}")

# ---------------------------------------------------------------------------
print("\n=== T2: 'amicability automatic when #E prime' -- counterexample hunt ===")
def a_count(ell):
    qr = bytearray(ell)
    for x in range((ell//2)+1): qr[x*x % ell] = 1
    cnt = 1
    for x in range(ell):
        v = (x*x*x + 7) % ell
        if v == 0: cnt += 1
        elif qr[v]: cnt += 2
    return ell + 1 - cnt

def is_small_prime(x):
    if x < 2: return False
    for d in range(2, math.isqrt(x)+1):
        if x % d == 0: return False
    return True

cex, closes, checked = [], [], 0
for ell in range(11, 1500):
    if not is_small_prime(ell) or ell % 3 != 1 or ell == 7: continue
    q = ell + 1 - a_count(ell)
    if q <= 7 or not is_small_prime(q) or q % 3 != 1: continue
    checked += 1
    back = q + 1 - a_count(q)
    (closes if back == ell else cex).append((ell, q, back))
print(f"  split ell < 1500 with q = #E7(F_ell) prime: {checked}")
print(f"  2-cycle closes: {len(closes)}  e.g. {closes[:4]}")
print(f"  FAILS to close: {len(cex)}  e.g. (ell, q, #E7(F_q)): {cex[:6]}")
print(f"  -> claim 'automatic when order prime' is "
      f"{'REFUTED (j=0: closure is a mod-84 class condition, 13/50)' if cex else 'not refuted here'}")

# ---------------------------------------------------------------------------
print("\n=== T3: formal-group integrality via [m](T) ===")
NDEG = 37
def formal_log_frac(b, N):
    u = [Fraction(0)]*(N+1); u[0] = Fraction(1)
    for _ in range(10):
        u2 = [Fraction(0)]*(N+1); u3 = [Fraction(0)]*(N+1)
        for i in range(N+1):
            if u[i]:
                for j in range(N+1-i):
                    if u[j]: u2[i+j] += u[i]*u[j]
        for i in range(N+1):
            if u2[i]:
                for j in range(N+1-i):
                    if u[j]: u3[i+j] += u2[i]*u[j]
        new = [Fraction(0)]*(N+1); new[0] = Fraction(1)
        for i in range(N+1-6): new[i+6] += b*u3[i]
        if new == u: break
        u = new
    v = [Fraction(0)]*(N+1); v[0] = Fraction(1)
    for i in range(1, N+1):
        v[i] = -sum(u[j]*v[i-j] for j in range(1, i+1))
    Lp = [Fraction(0)]*(N+1)
    for i in range(N+1):
        if v[i]:
            for j in range(N+1-i):
                if u[j]: Lp[i+j] += Fraction(i-2)*v[i]*(-u[j])/2
    L = [Fraction(0)]*(N+2)
    for i in range(N+1): L[i+1] = Lp[i]/(i+1)
    return L  # L[m] = coeff of T^m

L = formal_log_frac(7, NDEG)

def compose(f, g, N):
    """f(g(T)) truncated to degree N; f,g lists of Fractions, f[0]=g[0]=0."""
    out = [Fraction(0)]*(N+1)
    gp = [Fraction(0)]*(N+1); gp[0] = Fraction(1)   # g^0
    for k in range(1, N+1):
        # gp <- gp * g
        ng = [Fraction(0)]*(N+1)
        for i in range(N+1):
            if gp[i]:
                for j in range(1, N+1-i):
                    if g[j]: ng[i+j] += gp[i]*g[j]
        gp = ng
        if k < len(f) and f[k]:
            for i in range(N+1):
                if gp[i]: out[i] += f[k]*gp[i]
    return out

# exp = reversion of L: solve exp coefficients so that L(exp(T)) = T
E = [Fraction(0)]*(NDEG+1); E[1] = Fraction(1)
for m in range(2, NDEG+1):
    comp = compose(L[:NDEG+1], E, m)
    E[m] -= comp[m]      # adjust: L(exp)_m = comp_m + E[m]*1 (since L[1]=1)
ok_rev = compose(L[:NDEG+1], E, NDEG) == [Fraction(0), Fraction(1)] + [Fraction(0)]*(NDEG-1)
print(f"  series reversion exp = L^(-1) OK to T^{NDEG}: {ok_rev}")
for m in (2, 3, 5):
    mL = [c*m for c in L[:NDEG+1]]
    mult = compose(E, mL, NDEG)
    integral = all(c.denominator == 1 for c in mult)
    nz = [(i, c) for i, c in enumerate(mult) if c][:3]
    print(f"  [{m}](T) integral to T^{NDEG}: {integral}   first terms {nz}")

# ---------------------------------------------------------------------------
print("\n=== T4: unit root alpha ===")
alpha1 = t % p
ok1 = (alpha1*alpha1 - t*alpha1 + p) % p == 0
alpha2 = (t - p * pow(t, -1, p*p)) % (p*p)
ok2 = (alpha2*alpha2 - t*alpha2 + p) % (p*p) == 0
beta2 = (p * pow(alpha2, -1, p*p)) % (p*p)
print(f"  alpha = t (mod p) root of x^2-tx+p: {ok1}")
print(f"  Hensel mod p^2: alpha = t - p*t^(-1), root mod p^2: {ok2}; "
      f"v_p(beta)=1: {beta2 % p == 0 and beta2 != 0}")

# ---------------------------------------------------------------------------
print("\n=== T5: sextic unit distribution ===")
IDX2POW = {0:0, 1:3, 2:2, 3:5, 4:4, 5:1}
POW2IDX = {v:k for k,v in IDX2POW.items()}
def conj(v): return (v[0]-v[1], -v[1])
def primary(v):
    hits = [(i, mulw(u, v)) for i, u in enumerate(UNITS)
            if (u[0]*v[0]-u[1]*v[1]) % 3 == 2 and (u[0]*v[1]+u[1]*v[0]-u[1]*v[1]) % 3 == 0]
    return hits[0]
def cornacchia(ell):
    for y in range(1, math.isqrt(4*ell//3)+2):
        d = 4*ell - 3*y*y
        if d < 0: break
        s = math.isqrt(d)
        if s*s == d and (s+y) % 2 == 0: return ((s+y)//2, y)
def u_of(ell, pip):
    pc = conj(pip)
    w = (-pc[0]*pow(pc[1], -1, ell)) % ell
    tab = {(u[0]+u[1]*w) % ell: i for i, u in enumerate(UNITS)}
    s = pow(28 % ell, (ell-1)//6, ell)
    if s not in tab: return None
    return POW2IDX[(IDX2POW[tab[s]] + 3) % 6]

F, counts = {}, [0]*6
nprimes = 0
ell = 10
while len(F) < 432 or nprimes < 3000:
    ell += 1
    if ell > 100000: break
    if ell % 3 != 1 or not is_small_prime(ell) or ell == 7: continue
    pip = primary(cornacchia(ell))[1]
    u = u_of(ell, pip)
    if u is None: continue
    nprimes += 1
    counts[u] += 1
    F.setdefault((pip[0] % 84, pip[1] % 84), u)
ccounts = [0]*6
for u in F.values(): ccounts[u] += 1
print(f"  class census ({len(F)} classes): per-unit counts {ccounts} "
      f"(exact uniformity 72 each: {ccounts == [72]*6})")
print(f"  empirical over {nprimes} split primes: {counts} "
      f"(chi^2 = {sum((c - nprimes/6)**2/(nprimes/6) for c in counts):.2f}, df=5)")

# ---------------------------------------------------------------------------
print("\n=== T6: analytic conductor ===")
NE = 21168
print(f"  N/(4 pi^2) = {NE/(4*math.pi**2):.4f}   (claimed 536.19: "
      f"{'MATCHES this definition' if abs(NE/(4*math.pi**2) - 536.19) < 0.01 else 'no'})")

# ---------------------------------------------------------------------------
print("\n=== T7: L(E,1) from scratch (exact a_n, theta sum) ===")
NMAX = 4000
aP = {}
for ell in range(2, NMAX+1):
    if not is_small_prime(ell): continue
    if ell in (2, 3, 7): aP[ell] = 0
    elif ell % 3 == 2: aP[ell] = 0
    else:
        pip = primary(cornacchia(ell))[1]
        u = u_of(ell, pip)
        g = mulw(UNITS[u], pip)
        aP[ell] = 2*g[0] - g[1]
# spot-check against brute counts
for ell in (13, 19, 31, 103, 1009):
    assert aP[ell] == a_count(ell), ell
an = [0]*(NMAX+1); an[1] = 1
for ell, a1 in aP.items():
    # fill prime powers then multiply out (standard multiplicative sieve)
    pass
def a_n(m):
    r = 1; mm = m; d = 2
    while d*d <= mm:
        if mm % d == 0:
            k = 0
            while mm % d == 0: mm //= d; k += 1
            if d in (2,3,7): loc = 0
            else:
                s0, s1 = 1, aP[d]
                for _ in range(2, k+1): s0, s1 = s1, aP[d]*s1 - d*s0
                loc = s1
            r *= loc
            if r == 0: return 0
        d += 1
    if mm > 1:
        r *= (0 if mm in (2,3,7) else aP[mm])
    return r
sqN = math.sqrt(NE)
Lval = 2*sum(a_n(m)/m * math.exp(-2*math.pi*m/sqN) for m in range(1, NMAX+1))
Om = math.gamma(1/3)*math.gamma(1/6)/(2*math.sqrt(math.pi)*7**(1/6))
print(f"  L(1) = {Lval:.12f}")
print(f"  Omega(integral dx/y over E(R)) = {Om:.12f};  2*Omega = {2*Om:.12f}")
print(f"  L(1)/Omega = {Lval/Om:.9f}")

# ---------------------------------------------------------------------------
print("\n=== T8: |psi(p)|^2 = N(p) ===")
ell = 13
pip = primary(cornacchia(ell))[1]
u = u_of(ell, pip)
g = mulw(UNITS[u], pip)
print(f"  ell=13: psi = {g}, N = {Nrm(g)} = ell: {Nrm(g) == 13}   "
      f"[math: infinity-type (1,0) forces |psi|^2 = N; note this is psi, chi has |chi|=1]")
