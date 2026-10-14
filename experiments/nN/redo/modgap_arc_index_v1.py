"""modgap_arc_index_v1 (2026-10-06): where the cascade puts the 1/7 isolation when the arc criterion A fails.  Exact (Fractions).
For S = {m} + C (m = d_min) the 1/7-cascade of the full seven readings from 1/(7m) lands at the first instant at which C is
lonely at 1/7 and m is clear (`takeover_of_lonely_at` [L] for the bystander m).  In u = 7 m t, m is clear exactly on its
arcs [7k - 6, 7k - 1], k = 1, 2, ... [P].  A(S) is 'the landing lies in arc 1'.  Recorded: the arc index k of S's own landing
(walks that do not end within the cap are counted separately: the sets with no 1/7-lonely instant), for the 1,566 gcd-1
7-subsets of [1, 44] on which A is false (E415, modgap_arc_enum_v2_fails_top44.json).  The twelve exact real
counterexamples of E418 are E419's [T 12/12] (landing in arc 2), not re-run here.
Derivation check: the landing u* has m clear (u* in an arc) and C lonely at u* (exact).
"""
import sys, json, collections, math
from fractions import Fraction as F
sys.path.insert(0, '.')
from members_reach_check_v1 import cd

E7 = F(1, 7)


def cascade(S, t, cap=4000):
    for _ in range(cap):
        bl = [d for d in S if cd(d * t) < E7]
        if not bl:
            return t
        t = max(F(7 * round(d * t) + 1, 7 * d) for d in bl)
    return None


if __name__ == '__main__':
    out = open('modgap_arc_index_v1.out', 'w'); out.write(__doc__ + "\n")
    fl = [tuple(sorted(x)) for x in json.load(open('modgap_arc_enum_v2_fails_top44.json'))]
    c = collections.Counter(); chk = collections.Counter(); ex = collections.defaultdict(list)
    for S in fl:
        m = S[0]
        t = cascade(S, F(1, 7 * m))
        if t is None:
            c['no landing within cap'] += 1; continue
        u = 7 * m * t
        k = math.floor((u + 6) / 7)          # arc k is [7k-6, 7k-1]
        inarc = 7 * k - 6 <= u <= 7 * k - 1
        chk[(inarc and all(cd(d * t) >= E7 for d in S[1:]))] += 1
        c[k] += 1
        if len(ex[k]) < 3:
            ex[k].append((S, str(u)))
    out.write("(a) A false on [1,44]: %d sets; arc index of S's own 1/7 landing: %s\n" % (len(fl), dict(sorted(c.items(), key=str))))
    out.write("    derivation check (landing inside an arc of m, C lonely there): %s\n" % dict(chk))
    for k in sorted(ex, key=str):
        out.write("    arc %s examples: %s\n" % (k, ex[k]))
    out.close(); print(open('modgap_arc_index_v1.out').read()[len(__doc__):])
