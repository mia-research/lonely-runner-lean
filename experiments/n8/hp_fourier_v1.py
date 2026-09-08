r"""
hp_fourier_v1 -- the Fourier layer over the reformulation of hp_reformulation_v1.

sq(t) = +1 on [0,1/2), -1 on [1/2,1), period 1.   With theta = x/8 and e odd:
   beta_rho = bit0 of m_rho = [ floor(e_rho x/2) odd ] = (1 - sq(2 e_rho theta))/2
   alpha_rho= bit1 of m_rho = [ floor(e_rho x/4) odd ] = (1 - sq(  e_rho theta))/2

(T3)  <sq(a.)sq(b.)> = gcd(a,b)^2/(ab)  if v2(a)=v2(b), else 0.

O implies BOTH bit-columns of nu = m XOR mu are balanced (two 0s, two 1s), because a
permutation of {0,1,2,3} has each bit balanced.  With
   z^(0) = ( r_1, -r_3,  r_5, -r_7 ),  r = sq(2 e .)      (mu bit0 = 0,1,0,1)
   z^(1) = ( s_1,  s_3, -s_5, -s_7 ),  s = sq(  e .)      (mu bit1 = 0,0,1,1)
balance = [sum z = 0], and  1[sum z = 0] = 3/8 - e2(z)/8 + 3 e4(z)/8.

Averaging the two gives   o <= 3/8 + (c17 + c35)/4 + (3/8) P4,
   c_{ab} = gcd(e_a,e_b)^2/(e_a e_b),   P4 = < sq(e1.)sq(e3.)sq(e5.)sq(e7.) >,
because the pair-sign vectors cancel on every pair except {1,7} and {3,5}.

This script VERIFIES (T3), verifies |B0|,|B1| against direct exact computation,
computes P4 exactly, and evaluates the bound against the true o.
"""
import itertools, sys
from math import lcm, gcd
from fractions import Fraction as F
from nr2_core import o_measure

R4 = (1, 3, 5, 7)
MU = {1: 0, 3: 1, 5: 2, 7: 3}


def v2(n):
    k = 0
    while n % 2 == 0:
        n //= 2; k += 1
    return k


def sq_corr_exact(freqs):
    """exact < prod_i sq(f_i theta) > over theta in [0,1), by cells.
    sq(f theta) = +1 iff floor(2 f theta) even.  Breakpoints j/(2f)."""
    D = lcm(*[2 * f for f in freqs])
    pts = set()
    for f in freqs:
        step = D // (2 * f)
        pts.update(range(0, D, step))
    p = sorted(pts); p.append(D)
    tot = 0
    for i in range(len(p) - 1):
        a = p[i]
        val = 1
        for f in freqs:
            if ((2 * f * a) // D) % 2:
                val = -val
        tot += val * (p[i + 1] - a)
    return F(tot, D)


def sq_corr_formula(a, b):
    if v2(a) != v2(b):
        return F(0)
    return F(gcd(a, b) ** 2, a * b)


print("(T3) pair-correlation formula  < sq(a.)sq(b.) > = gcd^2/(ab) if v2 equal else 0")
bad = 0
for a in range(1, 26):
    for b in range(1, 26):
        if sq_corr_exact([a, b]) != sq_corr_formula(a, b):
            bad += 1
            if bad <= 5:
                print("   MISMATCH", a, b, sq_corr_exact([a, b]), sq_corr_formula(a, b))
print(f"   checked all 1 <= a,b <= 25: mismatches {bad}")


# ---- direct exact |B0|, |B1|, and the true o
def balance_measure(sp, bit):
    """measure of { theta : the bit-`bit` column of nu is balanced }"""
    mult = 4
    D = lcm(*[mult * e for e in sp])
    pts = set()
    for e in sp:
        step = D // (mult * e)
        pts.update(range(0, D, step))
    p = sorted(pts); p.append(D)
    tot = 0
    for i in range(len(p) - 1):
        a = p[i]
        st = tuple(((mult * e * a) // D) % mult for e in sp)
        col = [((m ^ MU[r]) >> bit) & 1 for m, r in zip(st, R4)]
        if sum(col) == 2:
            tot += p[i + 1] - a
    return F(tot, D)


def E2(sp, eps):
    tot = F(0)
    for i in range(4):
        for j in range(i + 1, 4):
            tot += eps[i] * eps[j] * F(gcd(sp[i], sp[j]) ** 2, sp[i] * sp[j])
    return tot


EPS0 = (1, -1, 1, -1)
EPS1 = (1, 1, -1, -1)

print("\n|B0|, |B1| from the Fourier formula vs direct exact computation")
tests = [(1,3,5,7),(1,11,5,7),(17,3,5,7),(9,3,21,15),(1,3,13,15),(1,19,21,39),
         (1,11,13,23),(41,43,13,15),(9,19,37,47),(33,27,13,7)]
print(f"{'tuple':>18} {'o':>12} {'|B0|':>12} {'formula':>12} {'|B1|':>12} {'formula':>12} {'P4':>10}")
for sp in tests:
    P4 = sq_corr_exact(list(sp))
    b0 = balance_measure(sp, 0); b1 = balance_measure(sp, 1)
    f0 = F(3, 8) - E2(sp, EPS0) / 8 + F(3, 8) * P4
    f1 = F(3, 8) - E2(sp, EPS1) / 8 + F(3, 8) * P4
    o = o_measure(sp)
    ok = (b0 == f0 and b1 == f1)
    print(f"{str(sp):>18} {str(o):>12} {str(b0):>12} {str(f0):>12} {str(b1):>12} {str(f1):>12} "
          f"{str(P4):>10}  {'ok' if ok else 'MISMATCH'}")

print("\nthe averaged bound   o <= 3/8 + (c17+c35)/4 + (3/8) P4")
print(f"{'tuple':>18} {'o':>10} {'bound':>10}  slack   (c17,c35,P4)")
for sp in tests:
    P4 = sq_corr_exact(list(sp))
    c17 = F(gcd(sp[0], sp[3]) ** 2, sp[0] * sp[3])
    c35 = F(gcd(sp[1], sp[2]) ** 2, sp[1] * sp[2])
    bnd = F(3, 8) + (c17 + c35) / 4 + F(3, 8) * P4
    o = o_measure(sp)
    print(f"{str(sp):>18} {float(o):>10.6f} {float(bnd):>10.6f}  {float(bnd-o):+.6f}"
          f"   ({c17}, {c35}, {P4})   valid={o<=bnd}")
