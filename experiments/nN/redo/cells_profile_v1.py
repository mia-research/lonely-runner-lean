import sys, pickle
from fractions import Fraction as F
from collections import Counter
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
J = int(sys.argv[1]); got = pickle.load(open('cell_members_J%d.pkl' % J, 'rb'))
C = Counter(); op = Counter(); lowb = upb = 0; n = 0; byop = {}; maxR = 0; rank1 = 0; dmin_win = Counter()
for i, rho in got:
    o = outcome(rho); s, j = o['opener'] if o['opener'] else (0, 0); nm = o['nmoves']; R = o['R']; maxR = max(maxR, R)
    strip = bool(j) and (8 * j - 1 < rho[s - 1] < 8 * j + 1); own = bool(j) and o['closer'][0] == s; z = o['width'] == 0
    C[('K0' if nm == 0 else 'K1' if nm == 1 else 'K2') + ('z' if z else '') + ('_strip' if strip else '') + ('_lap1' if j == 1 else '_lap>=2') + ('_closer=opener' if own else '')] += 1
    op[o['opener']] += 1; rank1 += (s == 1)
    dmin_win['[1,7]' if R <= 7 else '[9,15]' if R <= 15 else '>15'] += 1
    for r in rho:
        p = (R * r) % 8; n += 1
        if 1 <= p < F(5, 4): lowb += 1
        if F(27, 4) < p <= 7: upb += 1
print("J", J, "members", len(got), "max landing", float(maxR), "distinct openers", len(op), "rank-1 openers", rank1)
for k, v in sorted(C.items(), key=lambda x: -x[1]): print("  ", k, v)
print("d_min window of the landing:", dict(dmin_win))
print("positions in [1,1.25):", lowb, " in (6.75,7]:", upb, " of", n, "(uniform expectation each: %.0f)" % (n * 0.25 / 6))
print("openers with rank>=1 laps up to", max(j for (s, j) in op if s))
pickle.dump(op, open('openers_J%d.pkl' % J, 'wb'))
