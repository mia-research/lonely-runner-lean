"""modgap_aplike_v1 (2026-10-06): which residual fields exclude the nearly equal ('AP-like') clusters?  S = {m} + {c1 + i k : i = 0..5}, with m in M_SET (multiples of 840 and of 120, so that the divisibility fields q = 5, 6, 7, 8 can hold),
c1 from 26 m upward (rho = c1/m >= 26 as in the exceptions), k in K_SET.  The fields of the record's residual predicate (residual_members_v1.py `residual`) and the three added since (fast_pair, block_split, one_free; members_reach_check_v1)
are applied in the record's order and the FIRST failing field is recorded per set.  Exact integers.  Population: all (m, c1, k) of the grid; the table of first-failing fields, and the sets passing every field (printed individually)."""
import sys, itertools, collections, random
sys.path.insert(0, '.')
from math import gcd, lcm
from functools import reduce
import os
os.chdir('..')
src = open('residual_members_v1.py').read()
exec(src[:src.index("L = 8 * lcm")])
os.chdir('redo')
from members_reach_check_v1 import fast_pair, block_split, one_free
def fields(S):
    if len(set(S)) != 7: return 'distinct'
    if reduce(gcd, S) > 1: return 'common factor'
    if not any(d % 2 for d in S): return 'an odd reading'
    if not all(any(d % q == 0 for d in S) for q in (5, 6, 7, 8)): return 'q = 5,6,7,8 divide some reading'
    if not max(S) > 7 * min(S): return 'R1 (d_max <= 7 d_min)'
    if sum(4 if d % 8 == 4 else 2 for d in S if d % 8) < 8: return 'cost >= 8 (descent)'
    if any(free_flank8(S, e) for e in S if e % 8 == 0): return 'free flank'
    if shifted(S): return 'shifted flank'
    srt = sorted(S)
    if srt[-1] > 7 * srt[-2]: return 'fast runner (d7 > 7 d6)'
    if first_lap(S) or minus_seven(S): return 'first lap / minus seven'
    if has_rational_opening(S) or has_thirds(S) or has_fifths(S): return 'rational openings (N | 8, 3, 5)'
    if has_N(S, 6) or has_N(S, 7) or has_N(S, 9): return 'rational openings (N = 6, 7, 9)'
    if small_resolution(S): return 'small resolution D <= 64'
    if fast_pair(S): return 'fast pair'
    if block_split(S): return 'block split'
    if one_free(S): return 'one free'
    return 'PASSES ALL'
out = open('modgap_aplike_v1.out', 'w'); out.write(__doc__ + "\n")
rnd = random.Random(20261006)
cnt = collections.Counter(); passes = []; n = 0
for m in (120, 240, 360, 840, 1680, 2520):
    for rho in (26, 30, 40, 60):
        for _ in range(60):
            c1 = m * rho + rnd.randrange(0, m * 10)
            for k in (1, 2, 3, 5, 8, 13, 21, 37, 55, 89):
                S = tuple(sorted((m,) + tuple(c1 + i * k for i in range(6))))
                n += 1; f = fields(S); cnt[f] += 1
                if f == 'PASSES ALL' and len(passes) < 20: passes.append(S)
out.write("sets: %d\n" % n)
for k, v in sorted(cnt.items(), key=lambda kv: -kv[1]): out.write("  first failing field: %-44s %d\n" % (k, v))
for S in passes: out.write("  passes every field: %s\n" % (S,))
out.close(); print(open('modgap_aplike_v1.out').read()[len(__doc__):])
