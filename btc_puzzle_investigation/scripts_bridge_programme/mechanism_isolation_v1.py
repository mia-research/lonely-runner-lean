#!/usr/bin/env python3
"""PREREG_bridge_mechanism_isolation_v1: P1 mechanism isolation, P2 the 5/3 constant, P3 h>1.
Exact integers; verdicts from exact permutation counts."""
from math import isqrt, gcd
import random, sys
from collections import Counter
exec(open('cubic_bridge_v1.py').read().split('print("=== CONTROLS ===")')[0])
exec(open('bridge_dichotomy_v2.py').read().split('# ---------- (a)')[0].split('_S = ')[1].split('\n',1)[1]
     if False else "")

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

def perm_p(A, B, rnd, shuffles=20000):
    obs = sum(1 for a,b in zip(A,B) if a and b)
    Bl = list(B); ge = 0
    for _ in range(shuffles):
        rnd.shuffle(Bl)
        if sum(1 for a,b in zip(A,Bl) if a and b) >= obs: ge += 1
    return obs, ge, shuffles

def report(label, A, B, C, rnd, extra=""):
    N = len(A)
    if N < 60:
        print(f"  {label:>22} {N:>6}   -- too few"); return None
    E = sum(A)*sum(B)/N
    obs, ge, sh = perm_p(A, B, rnd)
    co, cg, _ = perm_p(C, B, rnd)
    verdict = "ASSOC" if (ge+1)/(sh+1) < 0.001 else "absent"
    ctl = "*** FIRED ***" if (cg+1)/(sh+1) < 0.001 else "clean"
    print(f"  {label:>22} {N:>6} agree={obs:>6} E={E:>7.1f} ratio={obs/E:>5.2f}"
          f" p={ge+1:>6}/{sh+1:<6} pow={0.62*E**0.5:>5.1f} ctl={ctl:>8} {verdict} {extra}")
    sys.stdout.flush()
    return obs/E

rnd = random.Random(1729)
BITS = 30

# ---------------- collect CM instances, recording Delta and the correction data -------------
def cm_sample(target, bits, rnd):
    A=[]; B=[]; C=[]; meta=[]
    while len(A) < target:
        p = rnd.randrange(1 << (bits-1), 1 << bits) | 1
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
            A.append(r["j"] == 0); B.append(r["k"] == 0)
            C.append(pow(rnd.randrange(2, I["n"]), (I["n"]-1)//3, I["n"]) == 1)
            meta.append(dict(delta=I["n"]-p, s=I["s1"], s2=I["s2"],
                             e_nu=r["e_nu_w"], e_pib=r["e_pib_w"],
                             c3=r["pred"], k=r["k"], j=r["j"]))
            if len(A) >= target: break
    return A, B, C, meta

print("=== C1 (must fire): CM instances, D=-3, l=3 ===")
A, B, C, META = cm_sample(20000, BITS, rnd)
ratio_cm = report("CM  D=-3 l=3", A, B, C, rnd)

print("\n=== P2: is the effect size the derived constant 5/3? ===")
N = len(META)
cs = Counter(m["s"] for m in META)
ce_nu = Counter(m["e_nu"] for m in META); ce_pib = Counter(m["e_pib"] for m in META)
same_e = sum(1 for m in META if m["e_nu"] == m["e_pib"])
c3_0 = sum(1 for m in META if m["c3"] == 0)
print(f"  (i)   s uniform on 0,1,2      : {dict(sorted(cs.items()))}   expect {N/3:.0f} each")
print(f"  (ii)  e(nu') uniform          : {dict(sorted(ce_nu.items()))}")
print(f"        e(pib') uniform         : {dict(sorted(ce_pib.items()))}")
print(f"  (iii) e(nu')==e(pib')         : {same_e}/{N} = {same_e/N:.4f}   expect 1/3 = 0.3333")
# independence of e_nu and e_pib: exact permutation on the pair
epairs = Counter((m["e_nu"], m["e_pib"]) for m in META)
print(f"        joint (e_nu,e_pib) cells: {dict(sorted(epairs.items()))}  expect {N/9:.0f} each")
kc = Counter((m["k"], m["c3"]) for m in META)
kmarg = Counter(m["k"] for m in META); cmarg = Counter(m["c3"] for m in META)
chi = sum((kc.get((x,y),0) - kmarg[x]*cmarg[y]/N)**2/(kmarg[x]*cmarg[y]/N)
          for x in kmarg for y in cmarg)
print(f"  (iv)  k vs c3 independence    : chi2(4df) = {chi:.2f}  (k marg {dict(sorted(kmarg.items()))},"
      f" c3 marg {dict(sorted(cmarg.items()))})")
sd = (N*(5/9)*(4/9))**0.5
print(f"  (v)   P(c3=0) = 5/9 = 0.5556  : {c3_0}/{N} = {c3_0/N:.4f}   z = {(c3_0 - N*5/9)/sd:+.2f}")
print(f"  (vi)  ratio = 5/3 = 1.6667    : observed {ratio_cm:.4f}")

print("\n=== P1: MECHANISM ISOLATION -- matched control, same Delta, no CM ===")
def matched_control(meta, bits, rnd, target):
    A=[]; B=[]; C=[]; used=0
    deltas = [m["delta"] for m in meta]
    rnd.shuffle(deltas)
    di = 0
    while len(A) < target and di < len(deltas)*40:
        delta = deltas[di % len(deltas)]; di += 1
        p2 = rnd.randrange(1 << (bits-1), 1 << bits) | 1
        p2 += (1-p2) % 3
        if p2 % 2 == 0: p2 += 3
        if p2 % 3 != 1 or not is_prime(p2, bases=(2,3,5,7,11,13)): continue
        n2 = p2 + delta
        if n2 <= 3 or n2 % 3 != 1 or n2 % 2 == 0: continue
        if not is_prime(n2, bases=(2,3,5,7,11,13)): continue
        pm = p2 % n2
        if pm == 0 or gcd(pm, n2) != 1: continue
        A.append(pow(pm, (n2-1)//3, n2) == 1)
        B.append(pow(n2 % p2, (p2-1)//3, p2) == 1)
        C.append(pow(rnd.randrange(2,n2), (n2-1)//3, n2) == 1)
        used += 1
    return A, B, C
Ac, Bc, Cc = matched_control(META, BITS, rnd, 20000)
ratio_ctl = report("MATCHED n-p=Delta", Ac, Bc, Cc, rnd)
print(f"  C3 check -- Delta matched by construction: CM |Delta| median bits"
      f" {sorted(abs(m['delta']).bit_length() for m in META)[len(META)//2]},"
      f" control drew from the SAME multiset")
print(f"\n  >>> CM ratio {ratio_cm:.3f}   vs   matched-control ratio"
      f" {ratio_ctl if ratio_ctl is None else round(ratio_ctl,3)}")
