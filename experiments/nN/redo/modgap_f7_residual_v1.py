"""modgap_f7_residual_v1 (2026-10-06): are the sets with no lonely instant at 1/7 (F7) inside EightResidual?  Population: the primitive and non-primitive F7 sets found in modgap_neartight_v1.out and _v2.out
(7-subsets of [1,24]; d_min in {1,2} of [1,30]).  For each: the record's Python mirror full_residual (all 22 fields, members_reach_check_v1) and, if not residual, which simple rule settles it:
R1 (d_max <= 7 d_min), R6 at q in {2,..,8} (no reading divisible by q), the common factor (gcd > 1: divide out, test the primitive part), 'fast' (d_max > 7 d_6, R8).  Exact integers."""
import sys, re, itertools
sys.path.insert(0, '.')
from math import gcd
from functools import reduce
from members_reach_check_v1 import full_residual
src = open('modgap_neartight_v2.out').read() + open('modgap_neartight_v1.out').read()
sets = sorted({tuple(map(int, m.group(1).split(','))) for m in re.finditer(r'(?:primitive|\()\s*:?\s*\(?([\d, ]{10,})\)', src)})
prim = sorted({tuple(map(int, m.group(1).split(','))) for m in re.finditer(r'primitive: \(([\d, ]+)\)', src)})
nonprim = sorted({tuple(map(int, t.split(','))) for t in re.findall(r"\(\(([\d, ]+)\), '", src)})
allf7 = sorted(set(prim) | set(nonprim))
def reasons(S):
    S = tuple(sorted(S)); g = reduce(gcd, S)
    if g > 1: return ['common factor %d -> ' % g] + reasons(tuple(x // g for x in S))
    r = []
    if S[-1] <= 7 * S[0]: r.append('R1')
    for q in range(2, 9):
        if all(x % q for x in S): r.append('R6(q=%d)' % q)
    if S[-1] > 7 * S[-2]: r.append('fast R8')
    return r
out = open('modgap_f7_residual_v1.out', 'w'); out.write(__doc__ + "\n")
n_res = 0
for S in allf7:
    res = full_residual(S) if reduce(gcd, S) == 1 else None
    rs = reasons(S)
    n_res += bool(res)
    out.write("S=%s  delta<1/7  full_residual=%s  settled by: %s\n" % (S, res, rs if rs else 'none of R1/R6/R8 (needs another rule)'))
out.write("\nF7 sets listed: %d; in EightResidual (all 22 fields, primitive ones): %d; with no simple rule among R1/R6/R8 (after dividing a common factor): %d\n" %
          (len(allf7), n_res, sum(1 for S in allf7 if not [x for x in reasons(S) if not x.startswith('common')])))
out.close(); print(open('modgap_f7_residual_v1.out').read()[len(__doc__):][:6000])
