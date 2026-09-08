r"""
hp_iterated_v1 -- the ITERATED FIBRE (peeling) bound on o, with every constant explicit,
and an exact verification of each level.

Setting: normal form (hp_normal_form_v1).  nu_rho(y) = (floor(e_rho y) mod 4) XOR mu(rho).
Sort the speeds  f1 < f2 < f3 < f4  and peel the LARGEST last.

  D2 = { nu_{f1} != nu_{f2} }
  D3 = D2 n { nu_{f3} not in {nu_{f1}, nu_{f2}} }
  O  = D3 n { nu_{f4} = the missing value }

DISCREPANCY LEMMA (given): P periodic of period p and density delta, X a union of n
disjoint intervals  =>  | |X n P| - delta |X| | <= n delta(1-delta) p.

For a fixed value c, { nu_rho = c } = { floor(e_rho y) = c XOR mu(rho)  (mod 4) } is
periodic of period p = 4/e_rho, density 1/4, ONE interval per period.  Hence per
component the error is at most (1/4)(3/4)(4/e) = 3/(4e); a union of k such values gives
at most k * 3/(4e).

  LEVEL 1   |D2|  <= 3/4 + 3 f1 /(4 f2)                       [complement: 1 value]
  LEVEL 2   |D3|  <= |D2|/2 + 3 n(D2) /(2 f3)                 [2 values]
  LEVEL 3   o     <= |D3|/4 + 3 n(D3) /(4 f4)                 [1 value]

  n(D2) <= f1 + f2 - 1,      n(D3) <= f1 + f2 + f3 - 2        (cells of the sub-grids)

Closed form:
  o <= 3/32 + 3 f1/(32 f2) + 3 (f1+f2-1)/(8 f3) + 3 (f1+f2+f3-2)/(4 f4).

This script verifies the three level inequalities with the EXACT n(D2), n(D3) and then
the closed form, on exhaustive and random tuples.  Exact Fractions.
"""
import itertools, sys, random
from math import lcm, gcd
from fractions import Fraction as F

MU = {1: 0, 3: 1, 5: 2, 7: 3}


def levels(sp):
    """sp = (e_1,e_3,e_5,e_7) indexed by residue.  Returns
       (|D2|, n(D2), |D3|, n(D3), o, f) with f = speeds sorted increasingly."""
    order = sorted(range(4), key=lambda i: sp[i])
    rhos = (1, 3, 5, 7)
    f = [sp[i] for i in order]
    mus = [MU[rhos[i]] for i in order]
    D = lcm(*sp)
    pts = set()
    for e in sp:
        pts.update(range(0, D, D // e))
    p = sorted(pts); p.append(D)
    d2 = d3 = o = 0
    n2 = n3 = 0
    prev2 = prev3 = False
    for i in range(len(p) - 1):
        a = p[i]; w = p[i + 1] - a
        nu = [(((f[k] * a) // D) % 4) ^ mus[k] for k in range(4)]
        in2 = nu[0] != nu[1]
        in3 = in2 and nu[2] not in (nu[0], nu[1])
        inO = len(set(nu)) == 4
        if in2:
            d2 += w
            if not prev2:
                n2 += 1
        if in3:
            d3 += w
            if not prev3:
                n3 += 1
        if inO:
            o += w
        prev2, prev3 = in2, in3
    return F(d2, D), n2, F(d3, D), n3, F(o, D), f


def check(sp):
    d2, n2, d3, n3, o, f = levels(sp)
    L1 = F(3, 4) + F(3 * f[0], 4 * f[1])
    L2 = d2 / 2 + F(3 * n2, 2 * f[2])
    L3 = d3 / 4 + F(3 * n3, 4 * f[3])
    C2 = f[0] + f[1] - 1
    C3 = f[0] + f[1] + f[2] - 2
    closed = (F(3, 32) + F(3 * f[0], 32 * f[1]) + F(3 * C2, 8 * f[2])
              + F(3 * C3, 4 * f[3]))
    return dict(o=o, d2=d2, n2=n2, d3=d3, n3=n3, L1=L1, L2=L2, L3=L3,
                closed=closed, nb2=C2, nb3=C3,
                ok1=(d2 <= L1), ok2=(d3 <= L2), ok3=(o <= L3),
                okn2=(n2 <= C2), okn3=(n3 <= C3), okc=(o <= closed))


tests = [(1,3,5,7),(1,11,5,7),(17,3,5,7),(9,3,21,15),(1,3,13,15),(1,19,21,39),
         (1,11,13,23),(41,43,13,15),(9,19,37,47),(33,27,13,7),(1,3,45,47),
         (1,11,5,151),(1,3,5,1007),(9,19,101,4001),(1,19,401,16001)]
print(f"{'tuple':>22} {'o':>9} {'L3 bnd':>9} {'closed':>9}  lvl-ok  closed<1/2")
for sp in tests:
    r = check(sp)
    print(f"{str(sp):>22} {float(r['o']):>9.6f} {float(r['L3']):>9.6f} "
          f"{float(r['closed']):>9.4f}  "
          f"{r['ok1']}{r['ok2']}{r['ok3']}{r['okn2']}{r['okn3']}{r['okc']}   "
          f"{r['closed'] < F(1,2)}")

print("\nexhaustive validity sweep of all five inequalities")
bad = {k: 0 for k in ('ok1','ok2','ok3','okn2','okn3','okc')}
n = 0; closed_ok = 0
for qs in itertools.product(range(6), repeat=4):
    sp = tuple(8 * q + r for q, r in zip(qs, (1, 3, 5, 7)))
    if len(set(sp)) != 4:
        continue
    n += 1
    r = check(sp)
    for k in bad:
        if not r[k]:
            bad[k] += 1
    if r['closed'] < F(1, 2):
        closed_ok += 1
print(f"   {n} tuples (q <= 5): violations {bad}")
print(f"   closed-form bound < 1/2 for {closed_ok} of {n} ({100*closed_ok/n:.2f}%)")

print("\nrandom large-speed sweep")
random.seed(3)
n = 0; bad2 = 0; closed_ok = 0
for _ in range(4000):
    sp = tuple(8 * random.randrange(0, 400) + r for r in (1, 3, 5, 7))
    if len(set(sp)) != 4:
        continue
    n += 1
    r = check(sp)
    if not all(r[k] for k in bad):
        bad2 += 1
    if r['closed'] < F(1, 2):
        closed_ok += 1
print(f"   {n} random tuples speeds < 3200: violations {bad2}; "
      f"closed-form < 1/2 for {closed_ok} ({100*closed_ok/n:.2f}%)")

print("\nlacunary family (f_{k+1} ~ K f_k): the bound does close")
for K in (2, 4, 8, 16, 32, 64):
    sp = (1, 8 * K + 3, 8 * K * K + 5, 8 * K ** 3 + 7)
    r = check(sp)
    print(f"   K={K:3d}  {str(sp):>28} o={float(r['o']):.6f} closed={float(r['closed']):.6f}"
          f"  <1/2: {r['closed'] < F(1,2)}")
