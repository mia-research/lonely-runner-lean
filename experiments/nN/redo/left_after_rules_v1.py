"""E407 (2026-10-06), left_after_rules_v1: the stored residual members (all 22 fields) that no current rule
settles: not the Lean residue cases with M(2,2) (lean_case_reach_v2.settled, conditional M(1,3) also counted as
settled here), not the grid corollary (lean_case_reach_v3.grid), not the descent by q (descent_mod_q_reach_v1.rule_q).
Recorded, exactly (Fractions; the floats printed are for reading only): the cascade's landing in cascade
coordinates R* = 8 d_min t*, the opener's rank and class, and the separation profile (s1/s0 against 9 and 26,
and the spread s6/s1 of the six faster readings).
"""
import sys, collections, math
out = open("left_after_rules_v1.out", "w")
from fractions import Fraction as F
sys.path.insert(0, '.')
from members_reach_check_v1 import load, full_residual, cascade, E8
from lean_case_reach_v2 import settled, typ
from lean_case_reach_v3 import grid
from descent_mod_q_reach_v1 import rule_q
for fn in ['../residual_members_C_list_v1.json', 'both_shadowed_members_v1.json']:
    sets = [S for S in dict.fromkeys(load(fn)) if full_residual(S)]
    left = []
    for S in sets:
        mult = [d for d in S if d % 8 == 0]; rs = tuple(sorted(d % 8 for d in S if d % 8))
        if settled(len(mult), rs, 'both') or grid(S) or rule_q(S): continue
        left.append(S)
    c = collections.Counter(); ex = []
    for S in left:
        s = sorted(S); t = cascade(list(S)); R = 8 * s[0] * t
        op = [d for d in S if d * t - math.floor(d * t) == E8]
        oprank = s.index(op[0])
        c[('opener rank', oprank, 'opener mult8' if op[0] % 8 == 0 else 'opener non-mult')] += 1
        c[('R* < 2' if R < 2 else 'R* >= 2')] += 1
        if len(ex) < 6: ex.append((tuple(s), t, 'R*=%s' % R, 'opener', op))
    out.write('%s left %d\n' % (fn, len(left))); print(fn, 'left', len(left)); [print('  ', k, v) for k, v in sorted(c.items(), key=str)]
    for e in ex[:4]: print('  ', e)

print('--- separation profile of the left members (exact comparisons) ---')
for fn in ['../residual_members_C_list_v1.json', 'both_shadowed_members_v1.json']:
    sets = [S for S in dict.fromkeys(load(fn)) if full_residual(S)]
    c = collections.Counter(); rmin = None; rmax = None; smax = None
    for S in sets:
        mult = [d for d in S if d % 8 == 0]; rs = tuple(sorted(d % 8 for d in S if d % 8))
        if settled(len(mult), rs, 'both') or grid(S) or rule_q(S): continue
        s = sorted(S); r = F(s[1], s[0]); spread = F(s[6], s[1])
        c[('slowest is a multiple of 8', s[0] % 8 == 0)] += 1
        c[('ratio s1/s0 >= 9', r >= 9)] += 1
        c[('ratio s1/s0 >= 26', r >= 26)] += 1
        c[('fast spread s6/s1 <= 7', spread <= 7)] += 1
        rmin = r if rmin is None or r < rmin else rmin; rmax = r if rmax is None or r > rmax else rmax
        smax = spread if smax is None or spread > smax else smax
    print(fn, dict(sorted(c.items(), key=str)), 'min s1/s0 = %.3f, max s1/s0 = %.3f, max s6/s1 = %.3f' % (float(rmin), float(rmax), float(smax)))
