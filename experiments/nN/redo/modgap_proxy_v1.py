"""modgap_proxy_v1 (2026-10-06): is the opener-closer pair a proxy?  Controls for modgap_farey_v1.  Exact.
[P] the least-denominator rational a/q of [t*, t_R] is a Stern-Brocot ancestor of EVERY point of [t*, t_R], so 'D <= 1 from the mediant' is not specific
to the mediant.  Measured, per non-unit-fraction set of S1 (unique opener e and closer f):
  C1  n_Q = number of reduced rationals in [t*, t_R] with denominator <= e + f   (m = N/(e+f) is one; if n_Q is small the mediant claim is weak);
      and the share of sets where m is the only one, and where a/q != m.
  C2  every pair (d1, d2) of S (d1 <= d2), every integer N' with N'/(d1+d2) in [t*, t_R] at denominator d1+d2: the 'virtual mediants'.  How many pairs have
      one in the component, how many pairs have the opener-closer pair as the only one, how many of these virtual mediants equal a/q.
  C3  the pair that attains the least denominator among all virtual mediants in the component, against {opener, closer}: is the landing rational the
      least-denominator virtual mediant, and is the least-denominator pair {e, f}?
"""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from modgap_lib_v1 import cascade, openers, component, simplest, E8, E78
c = collections.Counter(); nQ = collections.Counter(); npairs = collections.Counter(); ex = []
for r in itertools.combinations(range(2, 25), 6):
    S = (1,) + r; t = cascade(S); tR, cl = component(S, t)
    if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
    op = openers(S, t)
    if len(op) != 1 or len(cl) != 1: continue
    e, f = op[0], cl[0]; sA = simplest(t, tR)
    N = int(e * t - E8) + int(f * tR - E78) + 1; m = F(N, e + f)
    # C1
    inQ = set()
    for q in range(1, e + f + 1):
        lo = math.ceil(t * q); hi = math.floor(tR * q)
        for a in range(lo, hi + 1):
            inQ.add(F(a, q))
    nQ[min(len(inQ), 6)] += 1
    c[('m is the only rational of denominator <= e+f in the component', len(inQ) == 1)] += 1
    c[('a/q != m', sA != m)] += 1
    # C2 / C3
    virt = {}
    for d1, d2 in itertools.combinations_with_replacement(S, 2):
        Dn = d1 + d2
        lo = math.ceil(t * Dn); hi = math.floor(tR * Dn)
        for Np in range(lo, hi + 1):
            v = F(Np, Dn)
            virt.setdefault(v, set()).add((d1, d2))
    nv = len(virt); npairs[min(nv, 8)] += 1
    pairsin = {p for ps in virt.values() for p in ps}
    c[('pairs with a virtual mediant in the component: 1 (only {e,f})', pairsin == {(min(e, f), max(e, f))})] += 1
    c[('a/q is a virtual mediant of some pair', sA in virt)] += 1
    c[('a/q is a virtual mediant of a pair other than {e,f}', sA in virt and any(p != (min(e, f), max(e, f)) for p in virt[sA]))] += 1
    least = min(virt, key=lambda v: v.denominator) if virt else None
    c[('least-denominator virtual mediant = a/q', least == sA)] += 1
    if sA != m and sA in virt and len(ex) < 12:
        ex.append((S, e, f, str(m), str(sA), sorted(virt[sA])))
out = open('modgap_proxy_v1.out', 'w'); out.write(__doc__ + "\n")
out.write("n_Q (number of rationals of denominator <= e+f in the component, capped at 6): %s\n" % dict(sorted(nQ.items())))
out.write("number of distinct virtual mediants in the component (capped at 8): %s\n" % dict(sorted(npairs.items())))
for k, v in sorted(c.items(), key=str): out.write("%s: %d\n" % (k, v))
out.write("examples where a/q != m and a/q is a virtual mediant (S, e, f, m, a/q, pairs):\n")
for e_ in ex: out.write("  %s\n" % (e_,))
out.close(); print(open('modgap_proxy_v1.out').read()[len(__doc__):])
