#!/usr/bin/env python3
"""
Probe v2 (2026-07-11): is the Hecke unit u(ell) a residue-class function of the
primary Frobenius mod 84 (the conductor norm 84 = 4*3*7)?  If yes, the amicable
2-cycle closure probability is an exactly computable rational, explaining the
measured 0.2902 (vs naive 1/6).

Steps:
  1. Build the empirical map  F : (primary pi mod 84) -> unit index, over all
     split primes r < 500000, and check single-valuedness (this is, in effect,
     an empirical sextic-reciprocity statement for (28/pi)_6).
  2. Check whether F collapses to a coarser modulus (28, 12, 21, 42).
  3. Compute the EXACT closure fraction over allowed classes mod 84 and compare
     with the direct empirical closure rate at 5*10^5.
"""

import math
from fractions import Fraction

UNITS = [(1,0), (-1,0), (0,1), (0,-1), (-1,-1), (1,1)]
IDX2POW = {0:0, 1:3, 2:2, 3:5, 4:4, 5:1}
POW2IDX = {v:k for k,v in IDX2POW.items()}

def mulw(a, b): return (a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0] - a[1]*b[1])
def Nrm(v): return v[0]*v[0] - v[0]*v[1] + v[1]*v[1]
def Tr(v):  return 2*v[0] - v[1]
def conj(v): return (v[0]-v[1], -v[1])
def uinv(i):  # inverse unit index
    return POW2IDX[(-IDX2POW[i]) % 6]

def primary(v):
    hits = [(i, mulw(u, v)) for i, u in enumerate(UNITS)
            if (u[0]*v[0]-u[1]*v[1]) % 3 == 2 and (u[0]*v[1]+u[1]*v[0]-u[1]*v[1]) % 3 == 0]
    assert len(hits) == 1
    return hits[0]   # (unit index applied, primary element)

def cornacchia(ell):
    for y in range(1, math.isqrt(4*ell//3) + 2):
        d = 4*ell - 3*y*y
        if d < 0: break
        s = math.isqrt(d)
        if s*s == d and (s+y) % 2 == 0:
            return ((s+y)//2, y)
    raise ValueError(ell)

def sieve(limit):
    bs = bytearray([1])*(limit+1); bs[0:2] = b'\x00\x00'
    for i in range(2, math.isqrt(limit)+1):
        if bs[i]: bs[i*i::i] = bytearray(len(bs[i*i::i]))
    return [i for i in range(limit+1) if bs[i]]

def u_of_prime(ell, pip):
    """unit index via validated formula u = zeta6^3 * ((28/pi)_6 conj)^1."""
    pipc = conj(pip)
    w = (-pipc[0] * pow(pipc[1], -1, ell)) % ell
    tab = {(u[0] + u[1]*w) % ell: i for i, u in enumerate(UNITS)}
    s = pow(28 % ell, (ell-1)//6, ell)
    if s not in tab: return None
    return POW2IDX[(IDX2POW[tab[s]] + 3) % 6]

LIM = 500_000
ps = sieve(LIM)
splits = [r for r in ps if r % 3 == 1 and r > 7]

# --- 1. class map mod 84 -----------------------------------------------------
F = {}
viol = 0
for r in splits:
    pip = primary(cornacchia(r))[1]
    u = u_of_prime(r, pip)
    if u is None: continue
    key = (pip[0] % 84, pip[1] % 84)
    if key in F and F[key] != u: viol += 1
    F.setdefault(key, u)
print(f"1. classes mod 84 observed: {len(F)}; single-valuedness violations: {viol}"
      f"  -> {'u IS a class function mod 84' if viol == 0 else 'NOT a class function'}")

# --- 2. coarser moduli -------------------------------------------------------
for M in (28, 12, 21, 42):
    cmap, v = {}, 0
    for (x, y), u in F.items():
        k = (x % M, y % M)
        if k in cmap and cmap[k] != u: v += 1
        cmap.setdefault(k, u)
    print(f"2. modulus {M}: {len(cmap)} classes, violations {v}"
          f"{'  -> collapses to mod ' + str(M) if v == 0 else ''}")

# --- 3. exact closure fraction over classes mod 84 ---------------------------
def coprime84(v):
    return math.gcd(Nrm(v), 84) == 1

if viol == 0:
    total = closing = missing = 0
    for key, u in F.items():
        gam = mulw(UNITS[u], key)                       # psi-Frobenius class
        one_minus = ((1 - gam[0]) % 84, (-gam[1]) % 84) # 1 - gamma mod 84
        if not coprime84(one_minus): continue           # q not coprime to 42
        total += 1
        ui2, piq = primary(one_minus)                   # piq = u' * (1-gamma)
        key2 = (piq[0] % 84, piq[1] % 84)
        if key2 not in F: missing += 1; continue
        # closure <=> U[F(key2)] * piq == 1 - gamma  <=>  F(key2) == inv(u')
        if F[key2] == uinv(ui2): closing += 1
    frac = Fraction(closing, total)
    print(f"3. exact class census: {closing}/{total} allowed classes close "
          f"= {frac} = {float(frac):.6f}  (unresolved classes: {missing})")

# --- empirical closure at 5e5 for comparison ---------------------------------
pset = set(ps)
def isprime_big(x):
    if x <= LIM: return x in pset
    import random
    random.seed(x)
    for q in ps[:60]:
        if x % q == 0: return False
    d, s = x-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for _ in range(20):
        a0 = random.randrange(2, x-1); yy = pow(a0, d, x)
        if yy in (1, x-1): continue
        for _ in range(s-1):
            yy = yy*yy % x
            if yy == x-1: break
        else: return False
    return True

def a_fast(ell):
    if ell <= 7 or math.gcd(ell, 84) != 1: return None
    pip = primary(cornacchia(ell))[1]
    u = u_of_prime(ell, pip)
    if u is None: return None
    return Tr(mulw(UNITS[u], pip))

tot = closed = 0
for ell in splits:
    aL = a_fast(ell)
    if aL is None: continue
    q = ell + 1 - aL
    if q <= 7 or q % 3 != 1 or not isprime_big(q): continue
    aQ = a_fast(q)
    if aQ is None: continue
    tot += 1
    if aQ == 2 - aL: closed += 1
print(f"   empirical at 5e5: {closed}/{tot} = {closed/tot:.4f}"
      + (f"  vs exact {float(frac):.4f} " if viol == 0 else ""))
