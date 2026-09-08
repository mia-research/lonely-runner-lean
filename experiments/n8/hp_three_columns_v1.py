r"""
hp_three_columns_v1 -- the EXACT characterisation

   O  =  B_0  n  B_1  n  B_01 ,

where B_chi = { theta : the chi-column of nu is balanced (two +1, two -1) } for the
three non-trivial characters chi of (Z/2)^2.  Reason: nu takes values in F_2^2 at the
four positions; a 4-tuple in F_2^2 is a permutation iff every non-trivial character
column is balanced.  (If A_0, A_1 are the bit-0/bit-1 supports then A_01 = A_0 sym A_1;
|A_01| = 2 exactly excludes A_0 = A_1 and A_0 = A_1^c, which are the only two ways a
both-columns-balanced tuple can fail to be a permutation.)

Each column indicator has the exact expansion  3/8 - e2/8 + 3 e4/8 in its own +-1
variables, so

   |B_0|  = 3/8 - E2(eps0; c)/8 + (3/8) P4          eps0  = (+,-,+,-)   c = <r r'>
   |B_1|  = 3/8 - E2(eps1; c)/8 + (3/8) P4          eps1  = (+,+,-,-)   c = <s s'>
   |B_01| = 3/8 - E2(eps01;d)/8 + (3/8) P8          eps01 = (+,-,-,+)   d = <r s r' s'>

with c_{ab} = gcd(e_a,e_b)^2/(e_a e_b),  P4 = <sq(e1.)sq(e3.)sq(e5.)sq(e7.)>,
P8 = < prod_rho sq(e_rho .) sq(2 e_rho .) >.

This script computes all of these exactly, checks the identity O = B0 n B1 n B01,
checks the closed forms, and reports  max over a sweep of  min(|B0|,|B1|,|B01|).
"""
import itertools, sys
from math import lcm, gcd
from fractions import Fraction as F
from nr2_core import o_measure

R4 = (1, 3, 5, 7)
MU = {1: 0, 3: 1, 5: 2, 7: 3}
EPS = {0: (1, -1, 1, -1), 1: (1, 1, -1, -1), 2: (1, -1, -1, 1)}


def columns(sp):
    """exact |B_0|, |B_1|, |B_01|, |B0 n B1 n B01| on the quadrant grid (entry eval)"""
    D = lcm(*[4 * e for e in sp])
    pts = set()
    for e in sp:
        pts.update(range(0, D, D // (4 * e)))
    p = sorted(pts); p.append(D)
    tot = [0, 0, 0, 0]
    for i in range(len(p) - 1):
        a = p[i]; w = p[i + 1] - a
        nu = [(((4 * e * a) // D) % 4) ^ MU[r] for e, r in zip(sp, R4)]
        b0 = sum(n & 1 for n in nu) == 2
        b1 = sum((n >> 1) & 1 for n in nu) == 2
        b2 = sum((n & 1) ^ ((n >> 1) & 1) for n in nu) == 2
        if b0: tot[0] += w
        if b1: tot[1] += w
        if b2: tot[2] += w
        if b0 and b1 and b2: tot[3] += w
    return [F(t, D) for t in tot]


def sq_corr(freqs):
    D = lcm(*[2 * f for f in freqs])
    pts = set()
    for f in freqs:
        pts.update(range(0, D, D // (2 * f)))
    p = sorted(pts); p.append(D)
    tot = 0
    for i in range(len(p) - 1):
        a = p[i]; v = 1
        for f in freqs:
            if ((2 * f * a) // D) % 2:
                v = -v
        tot += v * (p[i + 1] - a)
    return F(tot, D)


def closed_forms(sp):
    c = {}
    d = {}
    for i in range(4):
        for j in range(i + 1, 4):
            c[(i, j)] = F(gcd(sp[i], sp[j]) ** 2, sp[i] * sp[j])
            d[(i, j)] = sq_corr([sp[i], 2 * sp[i], sp[j], 2 * sp[j]])
    P4 = sq_corr(list(sp))
    P8 = sq_corr([f for e in sp for f in (e, 2 * e)])
    out = []
    for k, corr in ((0, c), (1, c), (2, d)):
        eps = EPS[k]
        E2 = sum(eps[i] * eps[j] * corr[(i, j)] for i in range(4) for j in range(i + 1, 4))
        E4 = P4 if k < 2 else P8
        out.append(F(3, 8) - E2 / 8 + F(3, 8) * E4)
    return out, P4, P8


tests = [(1,3,5,7),(1,11,5,7),(17,3,5,7),(9,3,21,15),(1,3,13,15),(1,19,21,39),
         (1,11,13,23),(41,43,13,15),(9,19,37,47),(33,27,13,7),(1,3,21,23),(1,3,45,47)]
print("identity  O = B0 n B1 n B01,  and the closed forms")
print(f"{'tuple':>18} {'o':>12} {'B0nB1nB01':>12} {'|B0|':>12} {'|B1|':>12} {'|B01|':>12} ok")
allok = True
for sp in tests:
    b = columns(sp); o = o_measure(sp)
    cf, P4, P8 = closed_forms(sp)
    ok = (o == b[3]) and all(b[i] == cf[i] for i in range(3))
    allok &= ok
    print(f"{str(sp):>18} {str(o):>12} {str(b[3]):>12} {str(b[0]):>12} {str(b[1]):>12} "
          f"{str(b[2]):>12} {ok}")
print("   all identities hold:", allok)

print("\n min(|B0|,|B1|,|B01|)  as an upper bound for o")
print(f"{'tuple':>18} {'o':>10} {'min|B|':>10} {'<1/2?':>6}   P4        P8")
for sp in tests:
    b = columns(sp); o = o_measure(sp)
    cf, P4, P8 = closed_forms(sp)
    m = min(b[0], b[1], b[2])
    print(f"{str(sp):>18} {float(o):>10.6f} {float(m):>10.6f} {str(m < F(1,2)):>6}"
          f"   {float(P4):+.5f}  {float(P8):+.5f}")

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 5
print(f"\nsweep q <= {QMAX}: distribution of min(|B0|,|B1|,|B01|)")
worst = None; nbad = 0; n = 0; worst_o = None
for qs in itertools.product(range(QMAX + 1), repeat=4):
    sp = tuple(8 * q + r for q, r in zip(qs, R4))
    if len(set(sp)) != 4:
        continue
    n += 1
    b = columns(sp)
    m = min(b[0], b[1], b[2])
    if m >= F(1, 2):
        nbad += 1
    if worst is None or m > worst[0]:
        worst = (m, sp, b[3])
    if worst_o is None or b[3] > worst_o[0]:
        worst_o = (b[3], sp)
print(f"   {n} tuples;  min|B| >= 1/2 for {nbad} of them")
print(f"   largest min|B| = {worst[0]} = {float(worst[0]):.6f} at {worst[1]} (o = {worst[2]})")
print(f"   largest o      = {worst_o[0]} = {float(worst_o[0]):.6f} at {worst_o[1]}")
