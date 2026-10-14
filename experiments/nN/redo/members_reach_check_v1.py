"""E400 (2026-10-05), members_reach_check_v1: the stored constructed residual members, re-checked against every
current EightResidual field, then sorted by the residue pattern of their non-multiples of 8: settled at type level,
settled by a drop (shift_cover_drop_v1), or left.  Exact integer arithmetic.

Fields: residual() of residual_members_v1 (v5's list, small resolution D <= 64, no common factor) plus the three
added later (residual_members_v5): no fast pair, no block split, no one free.  These mirror EightResidual's 22
fields in OrderEightCasesN.lean:770 (the Python mirror is the record's, not re-derived here).
For each settled member, the argument's instant is re-checked exactly (Fractions): type level at the cofactors'
first lonely instant, drop at 8 * (first lonely instant of S - W); failures listed.
Sources: ../residual_members_C_list_v1.json (547, built with 16 predicates), members_5978_v1.json,
both_shadowed_members_v1.json.
"""
import json, sys, math, itertools, collections
from fractions import Fraction as F
from functools import reduce
from math import gcd
sys.path.insert(0, '..'); sys.path.insert(0, '.')
import os
here = os.getcwd(); os.chdir('..')
src = open('residual_members_v1.py').read()
exec(src[:src.index("L = 8 * lcm")])
os.chdir(here)
from shift_cover_drop_v1 import type_coverable, drop_passes

def fast_pair(S):
    S = sorted(S); a = S[-2]
    return all(9 * c <= a for c in S[:-2])
def block_split(S):
    S = sorted(S)
    for r in range(1, 7):
        for Fb in itertools.combinations(S, r):
            g = reduce(gcd, Fb); rest = [c for c in S if c not in Fb]
            if rest and all(28 * c <= g for c in rest): return True
    return False
def one_free(S):
    return any((lambda g: g >= 2 and x % g)(reduce(gcd, [d for d in S if d != x])) for x in S)
def full_residual(S):
    return residual(S) and not fast_pair(S) and not block_split(S) and not one_free(S)

def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
E8 = F(1, 8)
def lonely(S, t): return all(cd(d * t) >= E8 for d in S)
def cascade(S):
    t = F(1, 8 * min(S))
    while True:
        bl = [d for d in S if cd(d * t) < E8]
        if not bl: return t
        t = max(F(8 * round(d * t) + 1, 8 * d) for d in bl)

def typ(nm): return ''.join(sorted('o' if d % 2 else ('t' if d % 4 == 2 else 'f') for d in nm))

def load(fn):
    d = json.load(open(fn)); sets = []
    if isinstance(d, dict):
        for v in d.values(): sets += v
    else: sets = d
    out = []
    for s in sets:
        if isinstance(s, dict):
            s = s.get('S') or s.get('set') or s.get('readings')
        if s and all(isinstance(x, int) for x in s): out.append(tuple(sorted(s)))
    return out

if __name__ == '__main__':
    out = open('members_reach_check_v1.out', 'w'); out.write(__doc__ + "\n")
    for fn in ['../residual_members_C_list_v1.json', 'members_5978_v1.json', 'both_shadowed_members_v1.json']:
        sets = list(dict.fromkeys(load(fn)))
        res = [S for S in sets if full_residual(S)]
        cnt = collections.Counter(); fails = []
        for S in res:
            mult = [d for d in S if d % 8 == 0]; nm = [d for d in S if d % 8]
            P = tuple(sorted(d % 8 for d in nm)); key = (len(mult), typ(nm))
            if len(mult) > 6: cnt[(key, 'more than six multiples')] += 1; continue
            if not type_coverable(P):
                tau = cascade([d // 8 for d in mult])
                ok = any(lonely(S, (tau + k) / 8) for k in range(8))
                cnt[(key, 'type level')] += 1
                if not ok: fails.append(S)
                continue
            W = None
            for size in range(1, len(P) + 1):
                for Wc in itertools.combinations(P, size):
                    if drop_passes(P, Wc)[0]: W = Wc; break
                if W: break
            if W:
                rest = list(nm)
                for r in W:
                    x = next(y for y in rest if y % 8 == r); rest.remove(x)
                t = cascade(mult + rest)
                ok = any(lonely(S, t + F(k, 8)) for k in range(8))
                cnt[(key, 'drop')] += 1
                if not ok: fails.append(S)
            else:
                cnt[(key, 'left')] += 1
        out.write("\n%s: stored %d distinct; in EightResidual (all 22 fields) %d\n" % (fn, len(sets), len(res)))
        for (key, how), n in sorted(cnt.items(), key=lambda x: (-x[1])):
            out.write("  shape %s pattern type %s: %s %d\n" % (key[0], key[1], how, n))
        out.write("  instant re-check failures: %d %s\n" % (len(fails), fails[:3]))
    out.close(); print(open('members_reach_check_v1.out').read()[len(__doc__):])
