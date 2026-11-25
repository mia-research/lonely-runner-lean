"""E948: the two 'swapped' ends, the frozen coincidence (2026-11-25).  Exact Fractions.
For E340 index 101498 and 101457, with reading 6 moved: at reading 7's exit at lap 5 (state R = 41/r_7 in units R = 8t),
is frozen reading 4 exactly at a zone edge?  And is the end r_6 = 33 r_7 / 41 (exit(6, lap 4) = exit(7, lap 5))?"""
import pickle
from fractions import Fraction as Fr
from math import floor, ceil
exec(open('island_ends_v2.py').read().split("mode = sys.argv[1]")[0])
for idx0 in (101498, 101457):
    rs = sorted(Fr(x) for x in rec[idx0][1])
    r4, r6, r7 = rs[3], rs[5], rs[6]
    t7 = Fr(41, 8) / r7
    x4 = r4 * t7
    print('E340 index', idx0, '| r_4 * t(exit 7, lap 5) =', x4, '~ %.15f' % float(x4), '| minus nearest m -/+ 1/8:', x4 - round(x4) - (E if x4 > round(x4) else -E))
    v = 33 * r7 / 41
    six = rs[:5] + rs[6:]
    print('   end candidate r_6 = 33 r_7/41 ~ %.15f; gate there %s; gate just below %s; actual r_6 ~ %.15f' % (float(v), gate(sorted(six + [v])), gate(sorted(six + [v - Fr(1, 10**30)])), float(r6)))
