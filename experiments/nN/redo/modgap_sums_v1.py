"""modgap_sums_v1 (2026-10-06): matched control for the mirror-pair rule RG.  [P] a mirror pair at a/q (gcd(a,q)=1) exists iff q divides some
pair sum d_i + d_j (i < j) or 2 d_i  (since r_i + r_j = a (d_i + d_j) mod q).  So RG is a statement about the divisors of the 28 sums
Sigma(S) = {d_i + d_j : i <= j}, which is a property of q alone, with no reference to the component.  Control, per non-unit-fraction S1 set:
for every q in [q_lo, q_hi] = [min denominator, max denominator] of the 'virtual' range, fraction of q that divide some element of Sigma(S);
compared with the share of sets whose actual a_A/q_A has q_A | some sum.  Also the same control restricted to q in a window of width 5 around q_A
(q_A - 2 .. q_A + 2, q >= 2), the nearest matched control.  Exact (integers)."""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from modgap_lib_v1 import cascade, component, simplest
tot = 0; hit = 0; win_hits = 0; win_n = 0; ratio = collections.Counter(); sets_rows = []
better = collections.Counter()
for r in itertools.combinations(range(2, 25), 6):
    S = (1,) + r; t = cascade(S); tR, cl = component(S, t)
    if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
    sA = simplest(t, tR); q = sA.denominator
    sums = {S[i] + S[j] for i in range(7) for j in range(i, 7)}
    div = lambda x: any(s % x == 0 for s in sums)
    tot += 1; hit += div(q)
    nb = [x for x in range(max(2, q - 2), q + 3) if x != q]
    win_n += len(nb); win_hits += sum(div(x) for x in nb)
    # for the set: share of neighbours with a mirror vs q itself
    better[(div(q), sum(div(x) for x in nb))] += 1
out = open('modgap_sums_v1.out', 'w'); out.write(__doc__ + "\n")
out.write("sets: %d; a_A/q_A has q_A | some pair sum: %d\n" % (tot, hit))
out.write("neighbouring moduli q_A-2..q_A+2 (excluding q_A): %d of %d divide some pair sum\n" % (win_hits, win_n))
out.write("(q_A divides a pair sum?, number of the 4 neighbouring moduli that do): %s\n" % dict(sorted(better.items())))
out.close(); print(open('modgap_sums_v1.out').read()[len(__doc__):])
