r"""
hp_resonance_limit_v1 -- the EXACT limit of o along a family carrying exactly one
low-height odd resonance.

Model.  o = |{ theta : nu(theta) is a permutation }| with nu_rho = floor(4 frac(e_rho
theta)) XOR mu(rho).  Write v_rho = frac(e_rho theta).  The point (v_rho) runs along
the closed geodesic of direction e on T^4.  Resonances n.e = 0 with SMALL height
|n_1 n_3 n_5 n_7| are the only ones that keep the geodesic away from equidistribution
at leading order; when the only low-height resonance is a single primitive n, the
leading-order law of (v_rho) is "uniform on the subtorus n.v = 0".

Under that law each v_rho = (j_rho + s_rho)/4 with j uniform on {0,1,2,3} and s
uniform on [0,1), independent, subject to the linear relation.  For n = (1,-1,-1,1):
     4 v_7 = 4(v_3 + v_5 - v_1)  =>  j_7 = (j_3 + j_5 - j_1 + d) mod 4,
     d = floor(s_3 + s_5 - s_1) in {-1,0,1} with P = 1/6, 2/3, 1/6.
Similarly for n = (1,1,-1,-1):  j_7 = (j_1 + j_3 - j_5 + d) mod 4, same d-law.
(1,-1,1,-1) is IMPOSSIBLE mod 8:  1 - 3 + 5 - 7 = -4 != 0 mod 8.

Everything below is exact Fractions.
"""
import itertools
from fractions import Fraction as F

MU = (0, 1, 2, 3)                      # for rho = 1,3,5,7
PD = {-1: F(1, 6), 0: F(2, 3), 1: F(1, 6)}


def limit(coeffs):
    """coeffs = (c1,c3,c5) with j_7 = (c1 j_1 + c3 j_3 + c5 j_5 + d) mod 4"""
    tot = F(0)
    for j1, j3, j5 in itertools.product(range(4), repeat=3):
        for d, p in PD.items():
            j7 = (coeffs[0] * j1 + coeffs[1] * j3 + coeffs[2] * j5 + d) % 4
            nu = (j1 ^ MU[0], j3 ^ MU[1], j5 ^ MU[2], j7 ^ MU[3])
            if len(set(nu)) == 4:
                tot += p
    return tot / 64


print("full-torus (no low resonance):        o_inf = 24/256 =", F(24, 256), "=", float(F(24,256)))
a = limit((-1, 1, 1))     # n = (1,-1,-1,1):  e1 + e7 = e3 + e5,  v7 = v3+v5-v1
b = limit((1, 1, -1))     # n = (1,1,-1,-1):  e1 + e3 = e5 + e7,  v7 = v1+v3-v5
print("one resonance e1+e7 = e3+e5:          o_inf =", a, "=", float(a))
print("one resonance e1+e3 = e5+e7:          o_inf =", b, "=", float(b))
print("65/256 =", float(F(65,256)))

# empirical convergence check on genuine tuples carrying exactly that resonance
from hp_omax_v1 import ou
print("\nempirical o along  e1 + e7 = e3 + e5  (e = (1+8a, 3+8b, 5+8c, 7+8(b+c-a)) )")
for (A, B, C) in [(0,1,2),(0,3,5),(1,5,9),(2,11,17),(3,20,31),(5,40,61),(7,80,121),(9,160,241)]:
    D = B + C - A
    sp = (1 + 8*A, 3 + 8*B, 5 + 8*C, 7 + 8*D)
    if len(set(sp)) < 4 or min(sp) <= 0:
        continue
    o, u = ou(sp)
    print(f"   {str(sp):>26} o = {float(o):.8f}   u = {float(u):.8f}   (o - {a} = {float(o-a):+.2e})")

print("\nempirical o along  e1 + e3 = e5 + e7")
for (A, B, C) in [(0,0,1),(1,4,7),(3,15,25),(6,45,75),(10,120,200),(15,300,500)]:
    # e1+e3 = e5+e7  ->  (1+8A)+(3+8B) = (5+8C)+(7+8D)  ->  8(A+B) + 4 = 8(C+D) + 12
    # => A + B = C + D + 1
    D = A + B - C - 1
    if D < 0:
        continue
    sp = (1 + 8*A, 3 + 8*B, 5 + 8*C, 7 + 8*D)
    if len(set(sp)) < 4:
        continue
    o, u = ou(sp)
    print(f"   {str(sp):>26} o = {float(o):.8f}   u = {float(u):.8f}   (o - {b} = {float(o-b):+.2e})")
