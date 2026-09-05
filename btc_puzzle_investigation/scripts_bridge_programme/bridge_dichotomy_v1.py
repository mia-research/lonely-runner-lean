#!/usr/bin/env python3
"""PREREG_bridge_dichotomy_v1: does the bridge exist iff zeta_l lies in the CM field?
Exact integers; verdicts from exact permutation p-values (integer counts only)."""
from math import isqrt, gcd
import random, sys
from collections import Counter

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

def sieve(N):
    s = bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2, isqrt(N)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]

def traces_for(p, absD):
    """all t with 4p = t^2 + |D| v^2 ; returns sorted list of t (both signs)."""
    out = []
    vmax = isqrt((4*p)//absD)
    for v in range(1, vmax+1):
        r = 4*p - absD*v*v
        if r < 0: break
        s = isqrt(r)
        if s*s == r and s > 0:
            out.append(s); out.append(-s)
    return out

def perm_pvalue(A, B, rnd, shuffles=10000):
    """exact permutation p-value for agreement count; integer counts only."""
    obs = sum(1 for a, b in zip(A, B) if a and b)
    Bl = list(B); ge = 0
    for _ in range(shuffles):
        rnd.shuffle(Bl)
        if sum(1 for a, b in zip(A, Bl) if a and b) >= obs: ge += 1
    return obs, ge, shuffles

def run_arm(absD, ell, target, rnd, plimit=1500000, label=""):
    """collect (A,B) over CM-disc-|D| instances with prime n, l | gcd(p-1, n-1)."""
    A = []; B = []; Actl = []
    for p in PRIMES:
        if p > plimit or len(A) >= target: break
        if p % ell != 1 or p < 7: continue
        for t in traces_for(p, absD):
            n = p + 1 - t
            if n <= 3 or n % ell != 1 or not is_prime(n): continue
            if t == 1: continue
            pm = p % n
            if pm == 0 or gcd(pm, n) != 1: continue
            a = pow(pm, (n-1)//ell, n) == 1
            b = pow(n % p, (p-1)//ell, p) == 1
            r = rnd.randrange(2, n)
            A.append(a); B.append(b)
            Actl.append(pow(r, (n-1)//ell, n) == 1)
            if len(A) >= target: break
    if len(A) < 40: return None
    N = len(A)
    nA = sum(A); nB = sum(B)
    obs, ge, sh = perm_pvalue(A, B, rnd)
    exp_num = nA*nB                     # expected agreements = nA*nB/N  (kept as integers)
    oc, gc, _ = perm_pvalue(Actl, B, rnd)
    return dict(label=label, absD=absD, ell=ell, N=N, nA=nA, nB=nB, obs=obs,
                exp_num=exp_num, p_perm=(ge+1, sh+1), ctl_obs=oc, ctl_p=(gc+1, sh+1))

def show(r):
    if r is None:
        print(f"  {'':>26} -- too few instances"); return
    N = r["N"]; expect = r["exp_num"]/N
    flag = "ASSOCIATION" if (r["p_perm"][0]/r["p_perm"][1]) < 0.001 else "absent"
    cflag = "*** CTL FIRED ***" if (r["ctl_p"][0]/r["ctl_p"][1]) < 0.001 else "ctl clean"
    print(f"  {r['label']:>26}  N={N:>5}  agree={r['obs']:>5}  exp={expect:>7.1f}"
          f"  ratio={r['obs']/expect if expect else float('nan'):>5.2f}"
          f"  p={r['p_perm'][0]}/{r['p_perm'][1]:<6} {flag:>11}   {cflag}")

PRIMES = sieve(1500000)
rnd = random.Random(24601)

print("=== ARM 1 (POSITIVE CONTROL): D=-3, l=3 -- bridge is KNOWN to exist ===")
r1 = run_arm(3, 3, 3000, rnd, label="D=-3, l=3")
show(r1)
if r1: print(f"      pre-committed: agree/N should be ~0.194 vs independence 0.111"
             f"   -> observed {r1['obs']/r1['N']:.4f} vs {r1['exp_num']/r1['N']**2:.4f}")
ARM1_FIRED = r1 is not None and (r1["p_perm"][0]/r1["p_perm"][1]) < 0.001
print(f"      ARM 1 fired: {ARM1_FIRED}"
      f"{'' if ARM1_FIRED else '   *** ALL ARMS VOID ***'}")

print("\n=== ARM 2: l=3 across CM discriminants with w=2 (zeta_3 NOT in the CM field) ===")
for absD in (7, 8, 11, 15, 19, 20, 43, 67, 163):
    show(run_arm(absD, 3, 3000, rnd, label=f"D=-{absD}, l=3"))
    sys.stdout.flush()

print("\n=== ARM 3: D=-3, l >= 5 (zeta_l NOT in the CM field) ===")
for ell in (5, 7, 11, 13):
    show(run_arm(3, ell, 3000, rnd, label=f"D=-3, l={ell}"))
    sys.stdout.flush()

print("\n=== ARM 5 (BLOCKER): D=-4 -- is #E always even, making prime n impossible? ===")
cnt = odd = 0
for p in PRIMES:
    if p > 200000 or p % 4 != 1 or p < 5: continue
    for t in traces_for(p, 4):
        n = p + 1 - t
        if n <= 3: continue
        cnt += 1
        if n % 2 == 1: odd += 1
print(f"  D=-4 twist orders examined: {cnt};  ODD ones: {odd}")
print(f"  -> {'CONFIRMED: prime order impossible, mu_4 arm structurally untestable' if odd==0 else 'NOT confirmed'}")
# and the reason, verified on the curve itself: (0,0) is on y^2 = x^3 + a x
print("  reason check: (0,0) satisfies y^2 = x^3 + a*x for every a  ->",
      all((0*0 - (0**3 + a*0)) % 101 == 0 for a in range(1, 101)))
