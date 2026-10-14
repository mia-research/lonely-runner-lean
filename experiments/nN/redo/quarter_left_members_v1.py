"""E426 (2026-10-07), quarter_left_members_v1: the divisible members (divisible_members_v2.json) that
quarter_coincidence_v1 leaves.  For each: the cofactor c1 that every odd reading divides, the quotients q_i = c1/w_i,
g = c1/lcm(q), and whether the descent by q of E407 (descent_mod_q_reach_v1.rule_q) applies, with its constructed
instant checked exactly (descent_mod_q_reach_v1.instant).  Exact integers and Fractions.
"""
import json, sys, collections
from math import lcm
sys.path.insert(0, '.')
from quarter_coincidence_v1 import quarter_pair
from descent_mod_q_reach_v1 import rule_q, instant
store = json.load(open('divisible_members_v2.json')); c = collections.Counter(); rows = []
for k in ('A', 'B'):
    for S in store[k]:
        S = tuple(S)
        if quarter_pair(S) is not False: continue
        M = sorted(d for d in S if d % 8 == 0); W = sorted(d for d in S if d % 2)
        c1s = [m // 8 for m in M if all((m // 8) % w == 0 for w in W)]
        c1 = c1s[0]; qs = [c1 // w for w in W]; g = c1 // lcm(*qs); q = rule_q(S)
        ok = q is not None and instant(S, q) is not None
        c[(k, 'one cofactor divided by every odd reading', bool(c1s), 'g >= 3', g >= 3, 'descent by q with an exact instant', ok)] += 1
        if len(rows) < 12: rows.append((k, qs, 'g digits %d' % len(str(g)), 'q = %s' % q))
out = open('quarter_left_members_v1.out', 'w'); out.write(__doc__ + "\n")
for kk, v in c.items(): out.write("%s: %d\n" % (kk, v))
for r in rows: out.write("  %s\n" % (r,))
out.close(); print(open('quarter_left_members_v1.out').read()[len(__doc__):])
