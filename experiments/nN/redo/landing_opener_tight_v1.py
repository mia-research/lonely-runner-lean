"""E401 (2026-10-05), landing_opener_tight_v1: how the cascade finds the isolation in the residual's
cost-exactly-8 patterns of shape (3,4): (o,o,o,o) and (o,o,t,t).  Exact (Fractions), stored members only.

Derived (by hand) before the run: with cost exactly 8 a cover of the eight shifts (tau + k)/8 is a perfect partition
(every non-multiple blocks its maximum, disjointly) [PROVISIONAL: covering; supports: the reading below].  At a tau where
an odd non-multiple w has w*tau whole, w blocks one shift only; where a non-multiple 2v (v odd) has 2v*tau an odd whole
number, it blocks none; either leaves a shift free.  At the cascade's landing t*, the opener e reads exactly 1/8:
  - e a non-multiple: with k* = floor(8 t*) and tau* = 8 t* - k*, e*tau* is a whole number  (forced, by the definition);
  - e = 8c a multiple: c*tau* = 1/8 mod 1, an edge of the cofactors' clear set.
Recorded per member: the opener's class (odd / 2 mod 4 / multiple of 8), and at tau* each non-multiple's blocked shift
set (exact), its size, and whether the eight shifts are covered at tau* by the non-multiples alone.
Pass condition (derivation check): for a non-multiple opener, its blocked set at tau* has size at most 1 (odd) or 0
(2 mod 4); listed failures would mean the derivation is wrong.
"""
import json, sys, math, itertools, collections
from fractions import Fraction as F
sys.path.insert(0, '.')
from members_reach_check_v1 import load, full_residual, cascade, cd, E8

def typ(d): return 'o' if d % 2 else ('t' if d % 4 == 2 else ('f' if d % 8 == 4 else 'm'))

def blocked(d, tau):
    return frozenset(k for k in range(8) if cd(d * (tau + k) / 8) < E8)

if __name__ == '__main__':
    out = open('landing_opener_tight_v1.out', 'w'); out.write(__doc__ + "\n")
    sets = []
    for fn in ['../residual_members_C_list_v1.json', 'both_shadowed_members_v1.json']:
        sets += load(fn)
    sets = list(dict.fromkeys(sets))
    want = {('o','o','o','o'), ('o','o','t','t')}
    rows = collections.Counter(); fails = []; ex = []
    for S in sets:
        if not full_residual(S): continue
        mult = [d for d in S if d % 8 == 0]; nm = [d for d in S if d % 8]
        ty = tuple(sorted(typ(d) for d in nm))
        if len(mult) != 3 or ty not in want: continue
        if ty == ('o','o','t','t'):
            ws = [d for d in nm if d % 2]
            if (ws[0] - ws[1]) % 8 not in (0,) and (ws[0] + ws[1]) % 8 != 0: continue   # only the same-class (left) patterns
        t = cascade(list(S))
        opener = [d for d in S if cd(d * t) == E8 and (d * t - math.floor(d * t)) == E8]   # at exactly +1/8 (leaving edge)
        k = math.floor(8 * t); tau = 8 * t - k
        Bs = {d: blocked(d, tau) for d in nm}
        cover = frozenset().union(*Bs.values()) == frozenset(range(8))
        cls = ','.join(sorted(set(typ(d) for d in opener))) or 'none at +1/8'
        sizes = tuple(sorted(len(b) for b in Bs.values()))
        rows[(''.join(ty), cls, sizes, cover)] += 1
        for d in opener:
            if d % 8 and ((d % 2 and len(Bs[d]) > 1) or (d % 4 == 2 and len(Bs[d]) > 0)):
                fails.append((S, d))
        if len(ex) < 6: ex.append((S, opener, t, sizes))
    for key, n in sorted(rows.items(), key=lambda x: -x[1]):
        out.write("type %s, opener class %s, blocked-set sizes at tau* %s, non-multiples cover all 8: %s -> %d\n" % (key[0], key[1], key[2], key[3], n))
    out.write("derivation-check failures: %d %s\n" % (len(fails), fails[:3]))
    for e in ex: out.write("  example %s opener %s t* = %s sizes %s\n" % e)
    out.close(); print(open('landing_opener_tight_v1.out').read()[len(__doc__):])
