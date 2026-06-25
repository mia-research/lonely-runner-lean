"""For each HALF-window read-off branch (i,j,c) the read-off only guarantees q>=36.
exc_open sees q>=30, so q in {30..35} is a sliver. Enumerate the sliver triples
(coprime, 3p<q, cone q<r<3q/2, relation 3r=iota*p+gamma*q) and find an explicit
R-witness m: fract(r/q(m+1/2)) in [1/6,1/2] AND fract(p/q(m+1/2)) in [1/6,1/3].
(A witness contradicts exc_open's h_nogood, closing the triple via exc_Rkill.)
Also list the CLEAN branches for completeness sanity.
"""
from math import gcd
from fractions import Fraction as F

# (i,j,c) half-window branches with (iota,gamma)
HALF = [
    ("(2,3) c4",  2,  4),
    ("(2,-3) c4", -2, 4),
    ("(4,3) c3",  4,  3),
    ("(4,-3) c5", -4, 5),
]

def fract(x):
    return x - (x.numerator // x.denominator)

def find_witness(p, q, r):
    for m in range(0, q):     # half-integer grid repeats with period q
        X = fract(F(r,1) / q * (F(m) + F(1,2)))
        A = fract(F(p,1) / q * (F(m) + F(1,2)))
        if F(1,6) <= X <= F(1,2) and F(1,6) <= A <= F(1,3):
            return m, X, A
    return None

for label, iota, gamma in HALF:
    print(f"\n##### {label}: 3r = {iota}p + {gamma}q,  q in 30..35")
    any_triple = False
    for q in range(30, 36):
        for p in range(1, q):
            if gcd(p, q) != 1 or 3 * p >= q:
                continue
            num = iota * p + gamma * q
            if num <= 0 or num % 3 != 0:
                continue
            r = num // 3
            if not (q < r and 2 * r < 3 * q):
                continue
            any_triple = True
            w = find_witness(p, q, r)
            if w is None:
                print(f"  q={q} p={p} r={r}: *** NO R-WITNESS ***")
            else:
                m, X, A = w
                print(f"  q={q} p={p} r={r}: witness m={m}  X={X} A={A}")
    if not any_triple:
        print("  (no sliver triples)")
