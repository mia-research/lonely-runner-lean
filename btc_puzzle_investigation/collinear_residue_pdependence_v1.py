#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
collinear_residue_pdependence_v1.py — what drives E[chi2(t^3-7)] over the secant-line family?

Candidates: (a) the cubic residuosity of B=7 mod p; (b) the twist trace t' of E': y^2 = x^3 - 7
(the uniform-t average is EXACTLY -t'/p by #E' = p+1+sum chi2); (c) non-uniformity of the t-multiset.

Full enumeration of ordered secant pairs at every prime p = 1 mod 3 in [40, 700]; exact integers.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from m40_n15_exact_accounting_v1 import legendre

def walk(p, B=7):
    n = p + 1 + sum(legendre((x * x % p * x + B) % p, p) for x in range(p))
    G = None
    for x in range(p):
        r = (x * x % p * x + B) % p
        if legendre(r, p) == 1:
            y = next(yy for yy in range(1, p) if yy * yy % p == r)
            G = (x, y); break
    def add(P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q
        if x1 == x2 and (y1 + y2) % p == 0: return None
        m = (3 * x1 * x1) * pow(2 * y1, p - 2, p) % p if P == Q else \
            (y2 - y1) * pow(x2 - x1, p - 2, p) % p
        x3 = (m * m - x1 - x2) % p
        return (x3, (m * (x1 - x3) - y1) % p)
    pts = [None] * n
    Q = None
    for d in range(n):
        pts[d] = Q
        Q = add(Q, G)
    return n, pts

def is_prime(m):
    for f in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % f == 0: return m == f
    i = 2
    while i * i <= m:
        if m % i == 0: return False
        i += 1
    return True

print("=" * 110)
print(" E[chi2(t^3-7)] over secant pairs vs candidate drivers  (full enumeration; p = 1 mod 3)")
print("=" * 110)
print(f" {'p':>4} {'p%9':>4} {'7cube':>5} | {'E[line]':>9} {'|E|*sqrt(p)':>11} | {'-t_prime/p':>10} | "
      f"{'t-multiset dev':>14}")
rows = []
for p in range(40, 700):
    if not is_prime(p) or p % 3 != 1:
        continue
    n, pts = walk(p)
    if not is_prime(n) or any(pts[d] is None for d in range(1, n)):
        continue                      # composite group order: walk machinery assumes prime n
    cube7 = pow(7, (p - 1) // 3, p) == 1
    # twist trace: #E' = p+1+sum chi2(t^3-7)  =>  sum = t'_neg... #E' = p+1+ S => S = #E'-p-1 = -t'
    S = sum(legendre((t * t % p * t - 7) % p, p) for t in range(p))
    tp_over_p = -S / p
    acc = 0; N = 0
    tfreq = {}
    for d1 in range(1, n):
        P1 = pts[d1]
        for d2 in range(1, n):
            if d1 == d2:
                continue
            P2 = pts[d2]
            if P1[0] == P2[0]:
                continue
            m = (P2[1] - P1[1]) * pow(P2[0] - P1[0], p - 2, p) % p
            t = (P1[1] - m * P1[0]) % p * pow(m, p - 2, p) % p
            acc += legendre((t * t % p * t - 7) % p, p)
            tfreq[t] = tfreq.get(t, 0) + 1
            N += 1
    E = acc / N
    # t-multiset non-uniformity: mean |freq/N - 1/p| (0 if t uniform)
    dev = sum(abs(c / N - 1 / p) for c in tfreq.values()) / p
    rows.append((p, p % 9, cube7, E, tp_over_p, dev))
    print(f" {p:>4} {p%9:>4} {str(cube7):>5} | {E:+9.4f} {abs(E)*p**0.5:11.3f} | {tp_over_p:+10.6f} | "
          f"{dev:14.6f}", flush=True)
print("-" * 110)
# correlation of E with cube-status
import statistics
cube = [r for r in rows if r[2]]; non = [r for r in rows if not r[2]]
print(f" primes with 7 CUBIC    : {len(cube):>2}  mean E = {statistics.fmean(r[3] for r in cube):+.4f}  "
      f"(nonzero: {sum(abs(r[3])>0.02 for r in cube)})")
print(f" primes with 7 NON-CUBIC: {len(non):>2}  mean E = {statistics.fmean(r[3] for r in non):+.4f}  "
      f"(nonzero: {sum(abs(r[3])>0.02 for r in non)})")
big = [r for r in rows if abs(r[3]) > 0.05]
print(f" primes with |E|>0.05: {[(r[0], 'cube' if r[2] else 'noncube') for r in big]}")
es = [abs(r[3]) for r in rows]; ps = [r[0] for r in rows]
# crude decay check: |E|*sqrt(p) trend quartiles
q = len(rows) // 4
print(f" |E|*sqrt(p) quartile means: {statistics.fmean(r[3]*r[0]**0.5 for r in rows[:q]):.2f} "
      f"{statistics.fmean(r[3]*r[0]**0.5 for r in rows[q:2*q]):.2f} "
      f"{statistics.fmean(r[3]*r[0]**0.5 for r in rows[2*q:3*q]):.2f} "
      f"{statistics.fmean(r[3]*r[0]**0.5 for r in rows[3*q:]):.2f}  "
      f"(constant => O(p^-1/2); growing => O(1))")
print("=" * 110)
