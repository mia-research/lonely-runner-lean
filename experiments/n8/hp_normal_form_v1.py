r"""
hp_normal_form_v1 -- the NORMAL FORM of o and u, and the resonance diagnosis.

NORMAL FORM (to be verified here).  For y in [0,1) put  M_rho(y) = floor(e_rho y) mod 4
and  nu_rho(y) = M_rho(y) XOR mu(rho),  mu(1),mu(3),mu(5),mu(7) = 0,1,2,3.  Then

    o = | { y in [0,1) : nu(y) is a permutation of {0,1,2,3} } |
    u = | { y : nu(y) and nu(y + 1/2) are both permutations } |      (y+1/2 mod 1)

RESONANCE DIAGNOSIS.  P4 = <sq(e1.)sq(e3.)sq(e5.)sq(e7.)> has the Fourier form
    P4 = (16/pi^4) * sum over ODD n in Z^4 with n.e = 0 of 1/(n1 n3 n5 n7),
so P4 is large exactly when the tuple carries a low-height ODD resonance.  Define
    H(e) = min { |n1 n3 n5 n7| : n odd, n.e = 0, n != 0 }.
Mod 8, an all-ones resonance can only have sign pattern (+,-,-,+) or (+,+,-,-) up to
global sign, i.e.  e_1 + e_7 = e_3 + e_5  or  e_1 + e_3 = e_5 + e_7;  the third pairing
e_1 + e_5 = e_3 + e_7 is IMPOSSIBLE because 1 - 3 + 5 - 7 = -4 is not 0 mod 8.
"""
import itertools, sys
from math import lcm, gcd
from fractions import Fraction as F
from nr2_core import o_measure, u_measure

R4 = (1, 3, 5, 7)
MU = {1: 0, 3: 1, 5: 2, 7: 3}


def normal_form(sp):
    """(o, u) from the normal form.  Breakpoints j/e and j/e + 1/2 -> denominator 2e."""
    D = lcm(*[2 * e for e in sp])
    pts = set()
    for e in sp:
        pts.update(range(0, D, D // (2 * e)))       # includes both j/e and j/e + 1/2 grids
    p = sorted(pts); p.append(D)
    def nu_at(a):
        return tuple((((e * a) // D) % 4) ^ MU[r] for e, r in zip(sp, R4))
    o = u = 0
    for i in range(len(p) - 1):
        a = p[i]; w = p[i + 1] - a
        perm_here = len(set(nu_at(a))) == 4
        b = (a + D // 2) % D
        perm_shift = len(set(nu_at(b))) == 4
        if perm_here:
            o += w
            if perm_shift:
                u += w
    return F(o, D), F(u, D)


def nf_audit(sp):
    """requirement (i) on the normal-form grid: no interior breakpoint, entry == exit."""
    D = lcm(*[2 * e for e in sp])
    pts = set()
    for e in sp:
        pts.update(range(0, D, D // (2 * e)))
    p = sorted(pts); p.append(D)
    ni = nm = 0
    for i in range(len(p) - 1):
        a, b = p[i], p[i + 1]
        for e in sp:
            lo = (a * e) // D; hi = (b * e) // D
            for k in range(lo + 1, hi + 1):
                if a * e < k * D < b * e:
                    ni += 1
            if (a * e) // D != (b * e) // D - (1 if (b * e) % D == 0 else 0):
                nm += 1
    return len(p) - 1, ni, nm


tests = [(1,3,5,7),(1,11,5,7),(17,3,5,7),(9,3,21,15),(1,3,13,15),(1,19,21,39),
         (1,11,13,23),(41,43,13,15),(9,19,37,47),(33,27,13,7),(1,11,13,7),(25,35,5,15)]
print("NORMAL FORM check")
print(f"{'tuple':>18} {'o(nr2)':>12} {'o(nf)':>12} {'u(nr2)':>12} {'u(nf)':>12}  cells int e!=x")
bad = 0
for sp in tests:
    o1, u1 = o_measure(sp), u_measure(sp)
    o2, u2 = normal_form(sp)
    nc, ni, nm = nf_audit(sp)
    bad += (o1 != o2 or u1 != u2)
    print(f"{str(sp):>18} {str(o1):>12} {str(o2):>12} {str(u1):>12} {str(u2):>12} "
          f"{nc:6d} {ni:3d} {nm:4d}  {'ok' if (o1==o2 and u1==u2) else 'MISMATCH'}")
print("   mismatches:", bad)

# ---- resonance height
def height(e, K=9):
    best = None; arg = None
    rng = [n for n in range(-K, K + 1) if n % 2]
    for n1 in rng:
        for n3 in rng:
            for n5 in rng:
                s = n1 * e[0] + n3 * e[1] + n5 * e[2]
                if s % e[3]:
                    continue
                n7 = -s // e[3]
                if n7 % 2 == 0 or abs(n7) > K:
                    continue
                h = abs(n1 * n3 * n5 * n7)
                if best is None or h < best:
                    best, arg = h, (n1, n3, n5, n7)
    return best, arg

print("\nRESONANCE HEIGHT H(e) = min |n1 n3 n5 n7| over odd n with n.e = 0  (|n_i| <= 9)")
print(f"{'tuple':>18} {'o':>10} {'H':>6} {'minimiser':>18}   a-priori rho0=4 ok?")
HALF = F(1, 2)
for sp in tests:
    h, arg = height(sp)
    o = o_measure(sp); u = u_measure(sp)
    apri4 = (u == 0) or (u + 2 * o <= HALF)
    apri26 = (o <= F(1, 4))
    print(f"{str(sp):>18} {float(o):>10.6f} {str(h):>6} {str(arg):>18}   "
          f"rho0=4:{apri4}  o<=1/4:{apri26}")
