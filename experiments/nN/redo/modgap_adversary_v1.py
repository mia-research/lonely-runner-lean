"""modgap_adversary_v1 (2026-10-06): an adversarial search for an EightResidual set with no lonely instant at 1/7 (guard against F17: a constructed-sample regularity taken as a law).  Construction aimed
at the near-tight family: a core C of five readings taken from the small readings of the 31 sets with no 1/7-lonely instant (modgap_neartight_v1/v2.out; all 5-subsets of the six smallest readings of
each, plus the primitive parts), and two fast readings L u, L u' with L = 8 lcm(1..64), 1 <= u < u' <= 7u (the construction of residual_members_v1.py, so that the fast pair rule does not apply).  Keep the
sets that pass full_residual (all 22 fields, Python mirror).  For each kept set: is it lonely at 1/7 (the 1/7-cascade of the full seven readings ends with no reading in the way, cap 400)?  Seeded; u up to
U_MAX.  Exact."""
import sys, re, itertools, collections, math, random
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd, lcm
from functools import reduce
from members_reach_check_v1 import full_residual
H = F(1, 7)
def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
def lonely7(S, cap=400):
    t = F(1, 7 * min(S))
    for _ in range(cap):
        B = [x for x in S if cd(x * t) < H]
        if not B: return True
        t = max(F(7 * round(x * t) + 1, 7 * x) for x in B)
    return None
src = open('modgap_neartight_v2.out').read() + open('modgap_neartight_v1.out').read()
f7 = sorted({tuple(map(int, m.group(1).split(','))) for m in re.finditer(r'primitive: \(([\d, ]+)\)', src)})
cores = set()
for S in f7:
    small = sorted(S)[:6]
    for C in itertools.combinations(small, 5): cores.add(C)
    for C in itertools.combinations(sorted(S), 5): cores.add(C)
L = 8 * lcm(*range(1, 65))
rnd = random.Random(20261006); U_MAX = 14
kept = collections.Counter(); notlonely = []; tried = 0; ex = []
for C in sorted(cores):
    for u in range(1, U_MAX + 1):
        for u2 in range(u + 1, 7 * u + 1):
            S = tuple(sorted(C + (L * u, L * u2))); tried += 1
            if not full_residual(S): continue
            r = lonely7(S); kept[r] += 1
            if r is None and len(notlonely) < 10: notlonely.append(S)
out = open('modgap_adversary_v1.out', 'w'); out.write(__doc__ + "\n")
out.write("cores: %d; sets tried: %d; in EightResidual (full_residual): %d; of these lonely at 1/7: %s\n" % (len(cores), tried, sum(kept.values()), dict((str(k), v) for k, v in kept.items())))
for S in notlonely: out.write("  residual and NOT 1/7-lonely: %s\n" % (S,))
out.close(); print(open('modgap_adversary_v1.out').read()[len(__doc__):])
