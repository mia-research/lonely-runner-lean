#!/usr/bin/env python3
"""PREREG_cubic_sextic_bridge_v1 -- Z[omega] machinery, controls K0-K3, Arms A/B/C.
Exact integers only. omega = (-1+sqrt(-3))/2 ; elements are (A,B) meaning A + B*omega.
"""
from math import isqrt, gcd
import random, sys
from collections import defaultdict

# ---------------- Z[omega] ----------------
def emul(x, y):
    (a,b),(c,d) = x,y
    return (a*c - b*d, a*d + b*c - b*d)          # omega^2 = -1-omega
def econj(x): a,b = x; return (a-b, -b)
def enorm(x): a,b = x; return a*a - a*b + b*b
UNITS = [((1,0),0,+1), ((0,1),1,+1), ((-1,-1),2,+1),
         ((-1,0),0,-1), ((0,-1),1,-1), ((1,1),2,-1)]   # (unit, s in omega^s, sign)
def primarize(lam):
    """return (primary multiple, s) with unit = (sign)*omega^s ; primary: A=2 mod3, B=0 mod3"""
    for u, s, sg in UNITS:
        m = emul(u, lam)
        if m[0] % 3 == 2 and m[1] % 3 == 0:
            return m, s
    return None, None

# ---------------- primality ----------------
_S = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113]
def is_prime(m, bases=(2,3,5,7,11,13,17,19,23,29,31,37)):
    if m < 2: return False
    for q in _S:
        if m % q == 0: return m == q
    d, s = m-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in bases:
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def cornacchia3(p, rnd):
    while True:
        g = rnd.randrange(2, p); w = pow(g, (p-1)//3, p)
        if w != 1: break
    r = (2*w+1) % p
    if r < p - r: r = p - r
    a, b = p, r; lim = isqrt(p)
    while b > lim: a, b = b, a % b
    c = p - b*b
    if c % 3: return None
    y2 = c//3; y = isqrt(y2)
    return (b, y) if y*y == y2 else None

# ---------------- cubic character ----------------
class Field:
    """Z[omega]/lambda  ~=  F_N ,  via omega -> wN = -A * B^{-1} mod N"""
    def __init__(self, lam, N):
        A, B = lam
        self.N = N
        self.w = (-A) * pow(B % N, -1, N) % N
        assert (self.w*self.w + self.w + 1) % N == 0, "K3 FAILED"   # control K3
        self.pw = [1, self.w, self.w*self.w % N]
    def emb(self, x):
        a, b = x
        return (a + b*self.w) % self.N
    def chi(self, x):
        """cubic residue character of x in Z[omega]; returns exponent e with chi = omega^e"""
        v = self.emb(x) if isinstance(x, tuple) else x % self.N
        if v % self.N == 0: return None
        r = pow(v, (self.N-1)//3, self.N)
        for e in (0,1,2):
            if r == self.pw[e]: return e
        raise AssertionError("not a cube root of unity")

def instance(p, t, rnd):
    """build pi, nu, pibar for the twist with trace t; returns dict or None"""
    if (4*p - t*t) % 3: return None
    v2 = (4*p - t*t)//3
    v = isqrt(v2)
    if v*v != v2 or v % 2 == 0 or t % 2 == 0: return None
    n = p + 1 - t
    if n <= 3 or not is_prime(n) or n % 3 != 1: return None
    if t == 1: return None                      # 1-t = 0
    pi   = ((t+v)//2, v)
    nu   = (1 - (t+v)//2, -v)
    pib  = ((t-v)//2, -v)
    if enorm(pi) != p or enorm(nu) != n or enorm(pib) != p: return None
    Fn = Field(nu, n); Fp = Field(pib, p)
    nup, s1 = primarize(nu)                     # nu'  = (+-omega^s1) * nu
    pibp, s2 = primarize(pib)                   # pib' = (+-omega^s2) * pib
    if nup is None or pibp is None: return None
    return dict(p=p, t=t, v=v, n=n, pi=pi, nu=nu, pib=pib, Fn=Fn, Fp=Fp,
                nup=nup, pibp=pibp, s1=s1, s2=s2)

def analyse(I):
    p, n, t, Fn, Fp = I["p"], I["n"], I["t"], I["Fn"], I["Fp"]
    j = Fn.chi(p % n)                    # chi_nu(p)      as omega_n^j
    k = Fp.chi((1-t) % p)                # chi_pibar(1-t) as omega_p^k
    # K0: Eisenstein reciprocity on the primarized pair
    jp = Fn.chi(I["pibp"]); kp = Fp.chi(I["nup"])
    # derived rule:  j - k = s1*e_pibar(omega) - s2*e_nu(omega)   (chi(-1)=1 always)
    e_nu_w  = Fn.chi((0,1))
    e_pib_w = Fp.chi((0,1))
    pred = (I["s1"]*e_pib_w - I["s2"]*e_nu_w) % 3
    return dict(j=j, k=k, jp=jp, kp=kp, pred=pred, diff=(j-k) % 3,
                e_nu_w=e_nu_w, e_pib_w=e_pib_w)

# ================================================================
rnd = random.Random(11235)

def collect(lo_bits, hi_bits, target, rnd):
    out = []
    while len(out) < target:
        if hi_bits <= 22:
            p = rnd.randrange(1 << (lo_bits-1), 1 << hi_bits) | 1
        else:
            p = rnd.randrange(1 << (hi_bits-1), 1 << hi_bits) | 1
        p += (1 - p) % 3
        if p % 2 == 0: p += 3
        if p % 3 != 1 or p < 7 or not is_prime(p, bases=(2,3,5,7,11,13)): continue
        rep = cornacchia3(p, rnd)
        if rep is None: continue
        a, b = rep
        if a*a + 3*b*b != p: continue
        for t in (a+3*b, -(a+3*b), a-3*b, -(a-3*b)):
            I = instance(p, t, rnd)
            if I is None: continue
            out.append(I)
            if len(out) >= target: break
    return out

print("=== CONTROLS ===")
train = collect(8, 18, 4000, rnd)
k0 = sum(1 for I in train if (lambda r: r["jp"] == r["kp"])(analyse(I)))
print(f"  K0 Eisenstein reciprocity chi_nu(pib') == chi_pib(nu') : {k0}/{len(train)}"
      f"   {'PASS' if k0==len(train) else '*** FAIL -- everything below is VOID ***'}")

# K1 Gauss: 2 is a cubic residue mod n  <=>  n = a^2 + 27 b^2
def rep_a2_27b2(n):
    for b in range(0, isqrt(n//27)+1):
        r = n - 27*b*b
        if r < 0: break
        s = isqrt(r)
        if s*s == r: return True
    return False
k1 = k1n = 0
for I in train[:1200]:
    n = I["n"]
    lhs = pow(2, (n-1)//3, n) == 1
    if lhs == rep_a2_27b2(n): k1 += 1
    k1n += 1
print(f"  K1 Gauss  2 cubic residue mod n <=> n = a^2+27b^2      : {k1}/{k1n}"
      f"   {'PASS' if k1==k1n else '*** FAIL ***'}")

base = sum(1 for I in train if analyse(I)["j"] == 0)
ctl  = sum(1 for I in train if pow(rnd.randrange(2, I["n"]), (I["n"]-1)//3, I["n"]) == 1)
print(f"  K2 base rate chi_3^(n)(p)=1 : {base}/{len(train)} = {base/len(train):.4f}"
      f"   CONTROL random base: {ctl/len(train):.4f}   (chance 0.3333)")
print(f"  K3 omega^2+omega+1 = 0 mod n and mod p : asserted per instance, {len(train)} instances PASS")

print("\n=== ARM A: derived bridge   j - k == s1*e_pib(w) - s2*e_nu(w)  (mod 3) ===")
def arm_a(rows, label):
    ok = sum(1 for I in rows if (lambda r: r["diff"] == r["pred"])(analyse(I)))
    print(f"  {label:>34}: {ok}/{len(rows)}   {'PASS' if ok==len(rows) else '*** VIOLATIONS ***'}")
    return ok == len(rows)
arm_a(train, "TRAIN p < 2^18")
for bits, tgt in ((22, 2000), (32, 1500), (64, 800), (128, 400), (256, 200)):
    rows = collect(bits, bits, tgt, rnd)
    arm_a(rows, f"OUT-OF-SAMPLE {bits} bits")
    sys.stdout.flush()
