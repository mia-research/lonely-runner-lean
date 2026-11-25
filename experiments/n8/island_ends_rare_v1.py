"""E948: the rare island ends of island_ends_v7, exactly (2026-11-25).  Exact Fractions.
(1) E340 66783, 66784, 67106: is r_6 = 7 exactly (so reading 6's lap-6 exit is R = 49/7 = 7, reading 1's zone entry)?
(2) E340 100406, reading 7 moved: state R0 = 17/r_2 (reading 2's lap-2 exit).  Which frozen reading has a zone edge exactly at R0?
    And on the crossing side just inside the end, what is in the way at reading 7's exit?"""
from fractions import Fraction as Fr
from math import floor, ceil
exec(open('island_ends_v2.py').read().split("mode = sys.argv[1]")[0])
for i in (66783, 66784, 67106):
    rs = sorted(Fr(x) for x in rec[i][1]); print('E340 index', i, '| r_6 =', rs[5], '| reading 6 lap-6 exit R =', 49 / rs[5])
i = 100406; rs = sorted(Fr(x) for x in rec[i][1]); R0 = 17 / rs[1]
print('E340 index', i, '| R0 = 17/r_2 =', R0, '~ %.12f' % float(R0))
for q in range(7):
    if q == 6: continue
    x = rs[q] * R0 / 8; m = round(x)
    print('   reading', q + 1, 'r =', rs[q], '| r R0/8 - nearest integer =', x - m, '(edge iff +-1/8)')
v = 49 * rs[1] / 17; six = rs[:6]
w = v - Fr(1, 10**20); r7 = sorted(six + [w]); t = (6 + E) / w
print('   end r_7 = 49 r_2/17 ~ %.15f; just inside (r_7 = end - 1e-20): at reading 7 exit R ~ %.15f in the way %s; gate %s' % (float(v), float(8 * t), [q + 1 for q in range(7) if blocked(r7[q], t)], gate(r7)))
