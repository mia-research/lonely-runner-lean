#!/usr/bin/env python3
"""freeze_n1_120deg_v1.py -- build the FROZEN sample for PREREG_n1_120deg_exact_ideal_v4.md.

EXACT INTEGER ARITHMETIC ONLY (folder OVERRIDE: no float in the signal path).
This script performs POINT-COUNTING ONLY (#E via Legendre symbols).  It computes NO
character sum V_1/V_2 -- so it legitimately runs BEFORE the first V_1, as the prereg
requires the freeze to.  Output: n1_120deg_FREEZE_v1.json  (SHA-256 printed at the end).

Selection rule (deterministic, from prereg v4 sec.3):
  STRATUM S  : first 10 primes p == 7 (mod 12), p > 547, n=#E(F_p) prime.
  STRATUM C  : first  5 primes p == 1 (mod 12), p > 547, n prime.
  IN-SAMPLE I: all primes p == 7 (mod 12), p <= 547, n prime  (reported separately).
Cells per prime: the (n-1)/6 cosets of mu_6 = <sixth-roots-of-unity mod n> in (Z/n)*.
  Class rep = least positive residue of the coset.  mu_6 is pinned per prime by
  recording zeta3 = the SMALLER nontrivial cube root of unity mod n.
Budget (frozen): per-prime 900 s wall, total 7200 s; ABSTAIN-and-don't-substitute.
"""
import json, hashlib

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
    """#E(F_p) for y^2 = x^3 + B, exact integer count (point-counting, NOT a V_k sum)."""
    n = p+1
    for x in range(p):
        n += legendre((x*x % p * x + B) % p, p)
    return n

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

def cube_root_of_unity(n):
    """smaller nontrivial cube root of unity mod n (n prime, n==1 mod 3), via sqrt(-3)."""
    rt = tonelli((-3) % n, n)                 # sqrt(-3) mod n
    inv2 = pow(2, n-2, n)
    c1 = (-1 + rt) * inv2 % n
    c2 = (-1 - rt) * inv2 % n
    assert (c1*c1 + c1 + 1) % n == 0 and (c2*c2 + c2 + 1) % n == 0
    return min(c1, c2)

def mu6(n, z3):
    """the six sixth-roots of unity mod n: {+-1, +-z3, +-z3^2}."""
    z3sq = z3*z3 % n
    S = {1 % n, (n-1) % n, z3, (n-z3) % n, z3sq, (n-z3sq) % n}
    assert len(S) == 6, (n, sorted(S))
    return sorted(S)

def class_count(n, z3):
    """number of mu_6 cosets in (Z/n)* = (n-1)/6, verified by explicit orbit enumeration."""
    U = mu6(n, z3)
    seen = [False]*n
    reps = []
    for m in range(1, n):
        if seen[m]: continue
        reps.append(m)
        for u in U:
            seen[m*u % n] = True
    assert len(reps) == (n-1)//6, (n, len(reps), (n-1)//6)
    return len(reps), reps

def gather(cond, count=None, pmax=None, B=7):
    out = []
    p = 2
    while True:
        p += 1
        if not is_prime(p): continue
        if pmax is not None and p > pmax: break
        if not cond(p): continue
        n = curve_order(p, B)
        if not is_prime(n): continue
        z3 = cube_root_of_unity(n)
        cells, _ = class_count(n, z3)
        out.append({"p": p, "n": n, "cells": cells, "zeta3_mod_n": z3})
        if count is not None and len(out) >= count:
            break
    return out

if __name__ == "__main__":
    IN   = gather(lambda p: p % 12 == 7, pmax=547)
    S    = gather(lambda p: p % 12 == 7 and p > 547, count=10)
    C    = gather(lambda p: p % 12 == 1 and p > 547, count=5)

    freeze = {
        "prereg": "PREREG_n1_120deg_exact_ideal_v4.md",
        "object": "E: y^2 = x^3 + 7 over F_p (j=0); L*(T) degree-4 twisted Frobenius poly",
        "primary_statistic": "g(p,a) = deg gcd(L*(T), L*(zeta3*T)) over Q(zeta_n, zeta3)",
        "prediction": "g = 2 at every census-surviving cell",
        "selection_rule": {
            "stratum_S": "first 10 primes p==7 mod 12, p>547, n=#E prime (PRIMARY, out-of-sample)",
            "stratum_C": "first 5 primes p==1 mod 12, p>547, n prime (cross-stratum control)",
            "in_sample_I": "all primes p==7 mod 12, p<=547, n prime (reported separately, never pooled)",
        },
        "cell_rule": "cells = (n-1)/6 cosets of mu_6=<6th roots of unity mod n> in (Z/n)*; "
                     "rep = least positive residue; mu_6 pinned by zeta3_mod_n (smaller nontrivial cube root)",
        "budget": {"per_prime_wall_s": 900, "total_wall_s": 7200,
                   "abstain_rule": "exceed cap -> ABSTAIN on that prime and all larger; never substitute"},
        "no_float": True,
        "strata": {"IN_SAMPLE_I": IN, "STRATUM_S": S, "STRATUM_C": C},
    }
    txt = json.dumps(freeze, indent=2, sort_keys=True)
    with open("n1_120deg_FREEZE_v1.json", "w") as f:
        f.write(txt + "\n")
    h = hashlib.sha256((txt + "\n").encode()).hexdigest()
    with open("n1_120deg_FREEZE_v1.json.sha256", "w") as f:
        f.write(h + "  n1_120deg_FREEZE_v1.json\n")

    print("IN-SAMPLE I (p==7 mod12, p<=547):", [d["p"] for d in IN])
    print("STRATUM  S (p==7 mod12, p>547) :", [d["p"] for d in S])
    print("STRATUM  C (p==1 mod12, p>547) :", [d["p"] for d in C])
    print()
    for name, st in (("IN",IN),("S",S),("C",C)):
        for d in st:
            print(f"  [{name}] p={d['p']:>5}  n={d['n']:>6}  cells=(n-1)/6={d['cells']:>4}  zeta3={d['zeta3_mod_n']}")
    print()
    print("SHA-256(n1_120deg_FREEZE_v1.json) =", h)
