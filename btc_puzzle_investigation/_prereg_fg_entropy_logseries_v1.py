#!/usr/bin/env python3
"""(a) exact H(d|R) collapse R1->R2 (Fraction arithmetic; log only for display)
   (b) formal-group logarithm of y^2=x^3+a6 in the uniformizer z=-x/y, over Q"""
import sys
from fractions import Fraction
from collections import Counter
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from t_y_maxbound_v1 import prime_order_curve, group_coords

print("---- (a) exact fiber collapse / conditional entropy, R1 -> R2 ----")
for lo, hi in [(150,250),(250,400),(400,550),(550,750),(900,1100),(1500,1700)]:
    r = prime_order_curve(lo, hi)
    if not r: continue
    p, n, G = r
    xs, ys = group_coords(G, p, n, 0)
    R1=[]; R2=[]
    for d in range(1, n):
        x,y = xs[d]%p, ys[d]%p
        r1 = x*pow(y,p-2,p)%p
        R1.append(r1); R2.append((r1+3*pow(r1,7,p))%p)
    c1, c2 = Counter(R1), Counter(R2)
    N = n-1
    # H(d|R) = sum_v (|fiber|/N) * log2(|fiber|)   (d uniform, R deterministic in d)
    import math
    H1 = sum(k*math.log2(k) for k in c1.values())/N
    H2 = sum(k*math.log2(k) for k in c2.values())/N
    # exact rational check that R2 is a function of R1 (fibers of R1 refine fibers of R2)
    m = {}
    refines = True
    for a,b in zip(R1,R2):
        if m.setdefault(a,b) != b: refines = False
    print(f"  p={p:5d} n={n:5d} | distinct R1={len(c1):4d} R2={len(c2):4d} "
          f"| H(d|R1)={H1:.4f} bits  H(d|R2)={H2:.4f} bits  dH=+{H2-H1:.4f} "
          f"| R2 is a function of R1: {refines}")

print("\n---- (b) formal group log of y^2 = x^3 + a6 in z = -x/y, coefficients over Q ----")
# w = z^3 + a6*w^3 solved iteratively; x=z/w, y=-1/w; omega = dx/(2y) = f(z) dz; log = int f
import sympy as sp
z, a6 = sp.symbols('z a6')
N = 26
w = sp.Integer(0)
for _ in range(6):
    w = sp.series(z**3 + a6*w**3, z, 0, N).removeO()
w = sp.expand(w)
x = sp.series(z/w, z, 0, N).removeO()
y = sp.series(-1/w, z, 0, N).removeO()
om = sp.series(sp.diff(x, z)/(2*y), z, 0, N).removeO()
print("  omega/dz =", sp.expand(sp.simplify(om)))
lg = sp.expand(sp.integrate(om, z))
print("  log_F(z) =", lg)
print("  log_F(z) at a6=7 :", sp.expand(lg.subs(a6, 7)))
