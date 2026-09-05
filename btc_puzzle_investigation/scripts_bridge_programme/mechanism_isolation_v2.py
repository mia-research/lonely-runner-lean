#!/usr/bin/env python3
"""v2: the exact laws behind the 5/3 constant (replacing the FALSE independence premise),
   plus P3 (h>1 discriminants). Exact integers only."""
from math import isqrt, gcd
import random, sys
from collections import Counter
exec(open('cubic_bridge_v1.py').read().split('print("=== CONTROLS ===")')[0])
exec(open('mechanism_isolation_v1.py').read().split('def perm_p')[0].split('def tonelli')[1]
     .join(['def tonelli','']) if False else "")

def tonelli(a, p):
    a %= p
    if a == 0: return 0
    if pow(a, (p-1)//2, p) != 1: return None
    if p % 4 == 3: return pow(a, (p+1)//4, p)
    q, s = p-1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while pow(z, (p-1)//2, p) != p-1: z += 1
    m, c, tt, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q+1)//2, p)
    while tt != 1:
        i, t2 = 0, tt
        while t2 != 1: t2 = t2*t2 % p; i += 1
        b = pow(c, 1 << (m-i-1), p)
        m, c = i, b*b % p
        tt = tt*c % p; r = r*b % p
    return r

def cornacchia_smith(p, absD):
    D = -absD
    x0 = tonelli(D % p, p)
    if x0 is None: return None
    if (x0 - D) % 2 != 0: x0 = p - x0
    a, b = 2*p, x0
    c = isqrt(4*p)
    while b > c: a, b = b, a % b
    r = 4*p - b*b
    if r % absD: return None
    v2 = r // absD
    v = isqrt(v2)
    if v*v != v2 or v == 0: return None
    return (b, v)

def prim_with_sign(lam):
    for u, s, sg in UNITS:
        m = emul(u, lam)
        if m[0] % 3 == 2 and m[1] % 3 == 0:
            return m, s, sg
    return None, None, None

rnd = random.Random(4096)
print("=== the exact laws behind 5/9 (replacing the falsified independence premise) ===")
rows = []
while len(rows) < 12000:
    p = rnd.randrange(1 << 25, 1 << 26) | 1
    p += (1-p) % 3
    if p % 2 == 0: p += 3
    if p % 3 != 1 or not is_prime(p, bases=(2,3,5,7,11,13)): continue
    rep = cornacchia3(p, rnd)
    if rep is None: continue
    a, b = rep
    if a*a+3*b*b != p: continue
    for t in (a+3*b, -(a+3*b), a-3*b, -(a-3*b)):
        I = instance(p, t, rnd)
        if I is None: continue
        r = analyse(I)
        _, s1, sg1 = prim_with_sign(I["nu"])
        _, s2, sg2 = prim_with_sign(I["pib"])
        rows.append(dict(t=t, s=s1, s2=s2, sg1=sg1, sg2=sg2,
                         e_nu=r["e_nu_w"], e_pib=r["e_pib_w"], c3=r["pred"],
                         j=r["j"], k=r["k"]))
        if len(rows) >= 12000: break
N = len(rows)
print(f"  instances: {N}   (26-bit p)")

# t = 1 mod 3 (already proved) -> m := (t-1)/3 is an integer
assert all((r["t"]-1) % 3 == 0 for r in rows)
for r in rows: r["m3"] = ((r["t"]-1)//3) % 3

v = sum(1 for r in rows if (r["e_nu"] + r["e_pib"]) % 3 == 2)
print(f"  (E1) e(nu')+e(pib') != 2 mod 3          : violations {v}/{N}"
      f"   {'EXACT LAW' if v==0 else '*** FALSE ***'}")
v = sum(1 for r in rows if ((r["s"] == 0) != ((r["e_nu"] + r["e_pib"]) % 3 == 1)))
print(f"  (E2) s=0  <=>  e(nu')+e(pib') = 1 mod 3 : violations {v}/{N}"
      f"   {'EXACT LAW' if v==0 else '*** FALSE ***'}")
# E3: e(pib') - e(nu') = +- (t-1)/3 mod 3 ?
tab = Counter(((r["e_pib"]-r["e_nu"]) % 3, r["m3"], r["sg1"]) for r in rows)
plus  = sum(1 for r in rows if (r["e_pib"]-r["e_nu"]) % 3 == r["m3"] % 3)
minus = sum(1 for r in rows if (r["e_pib"]-r["e_nu"]) % 3 == (-r["m3"]) % 3)
print(f"  (E3) e(pib')-e(nu') = +(t-1)/3 mod 3    : {plus}/{N}")
print(f"       e(pib')-e(nu') = -(t-1)/3 mod 3    : {minus}/{N}")
bysign = Counter((r["sg1"], ((r["e_pib"]-r["e_nu"]) - r["m3"]) % 3) for r in rows)
print(f"       split by unit sign (sign, diff-m3) : {dict(sorted(bysign.items()))}")
v = sum(1 for r in rows if (r["c3"] == 0) != (r["s"] == 0 or r["m3"] == 0))
print(f"  (E4) c3=0  <=>  (s=0 or 9 | t-1)        : violations {v}/{N}"
      f"   {'EXACT LAW' if v==0 else '*** FALSE ***'}")
n9 = sum(1 for r in rows if r["m3"] == 0)
print(f"       P(9 | t-1) = 1/3                   : {n9}/{N} = {n9/N:.4f}")
joint = Counter((r["s"] == 0, r["m3"] == 0) for r in rows)
print(f"       s=0 vs 9|(t-1) independence        : {dict(sorted(joint.items(), key=str))}"
      f"   expect {N/9:.0f} in the (True,True) cell")
c0 = sum(1 for r in rows if r["c3"] == 0)
sd = (N*(5/9)*(4/9))**0.5
print(f"  (E5) P(c3=0) = 1/3+1/3-1/9 = 5/9        : {c0}/{N} = {c0/N:.4f}"
      f"   z = {(c0-N*5/9)/sd:+.2f}")
agree = sum(1 for r in rows if r["j"]==0 and r["k"]==0)
E = sum(1 for r in rows if r["j"]==0)*sum(1 for r in rows if r["k"]==0)/N
print(f"  (E6) association ratio = 5/3 = 1.6667   : {agree/E:.4f}")

# ---------------- P3: h > 1 discriminants ----------------
def perm_p(A, B, rnd, shuffles=20000):
    obs = sum(1 for a,b in zip(A,B) if a and b)
    Bl = list(B); ge = 0
    for _ in range(shuffles):
        rnd.shuffle(Bl)
        if sum(1 for a,b in zip(A,Bl) if a and b) >= obs: ge += 1
    return obs, ge, shuffles

def sample_D(absD, ell, target, bits, rnd, cap=3000000):
    A=[];B=[];C=[]; tries=0
    while len(A) < target and tries < cap:
        tries += 1
        p = rnd.randrange(1 << (bits-1), 1 << bits)
        p -= (p % ell) - 1
        if p % 2 == 0: p += ell
        if p % ell != 1 or p < 7 or not is_prime(p, bases=(2,3,5,7,11,13)): continue
        rep = cornacchia_smith(p, absD)
        if rep is None: continue
        t0, v = rep
        for t in (t0, -t0):
            n = p+1-t
            if n <= 3 or n % ell != 1 or t == 1: continue
            if not is_prime(n, bases=(2,3,5,7,11,13)): continue
            pm = p % n
            if pm == 0: continue
            A.append(pow(pm,(n-1)//ell,n)==1); B.append(pow(n%p,(p-1)//ell,p)==1)
            C.append(pow(rnd.randrange(2,n),(n-1)//ell,n)==1)
            if len(A) >= target: break
    return A,B,C

print("\n=== P3: h > 1 discriminants (all = 5 mod 8), l = 3.  Prediction: absent (w=2) ===")
print(f"  {'D':>8} {'h':>3} {'N':>6} {'agree':>6} {'E':>7} {'ratio':>6} {'perm p':>13} {'power':>6} {'ctl':>7}")
H = {35:2, 51:2, 91:2, 115:2, 123:2, 187:2, 235:2, 267:2, 403:2, 427:2}
for absD in (35, 51, 91, 115, 123, 187, 235, 267, 403, 427):
    A,B,C = sample_D(absD, 3, 5000, 28, rnd)
    if len(A) < 60: print(f"  -{absD:>7} -- too few"); continue
    E = sum(A)*sum(B)/len(A)
    obs, ge, sh = perm_p(A,B,rnd); co, cg, _ = perm_p(C,B,rnd)
    print(f"  -{absD:>7} {H[absD]:>3} {len(A):>6} {obs:>6} {E:>7.1f} {obs/E:>6.2f}"
          f" {ge+1:>6}/{sh+1:<6} {0.62*E**0.5:>6.1f}"
          f" {'*FIRED*' if (cg+1)/(sh+1)<0.001 else 'clean':>7}"
          f"  {'ASSOC' if (ge+1)/(sh+1)<0.001 else 'absent'}")
    sys.stdout.flush()
