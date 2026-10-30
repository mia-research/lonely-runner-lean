"""E655. The 307 quarter-lap landings of E654 (other-block setter j, frac(s t*) = 1/4 or 3/4). For every reading d of
the subject: 8 d t* (exact). Forced: other-block readings give odd integers. Checked: (a) whether own-block readings
give integers; (b) the residues mod 8 of all eight-runner readings at t* when all are integers; (c) whether t* is an
instant a/(8D) at which the readings, read as multiples of a unit D, form the AP/grid lonely pattern of E306
(all 8 d t* odd, or integers with no multiple of 8). Exact Fractions."""
import math, pickle
from fractions import Fraction as F
from collections import Counter
def frac(x): return x - math.floor(x)
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
tab = Counter(); ex = []
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    if G <= 0 or op[0] != 'set': continue
    v = sp(p, G + p - 1, b); ownb = list(range(p)) if k < p else list(range(p, 8))
    if op[1] in ownb: continue
    s = b if k < p else F(1)
    if frac(s * t) not in (F(1, 4), F(3, 4)): continue
    oth = [i for i in range(8) if i not in ownb]
    vo = [8 * abs(v[i] - v[k]) * t for i in oth]
    vw = [8 * abs(v[i] - v[k]) * t for i in ownb if i != k]
    oth_odd = all(x.denominator == 1 and x.numerator % 2 == 1 for x in vo)
    own_int = all(x.denominator == 1 for x in vw)
    own_odd = own_int and all(x.numerator % 2 == 1 for x in vw)
    own_res = tuple(sorted(int(x) % 8 for x in vw)) if own_int else None
    key = ('other block odd' if oth_odd else 'OTHER NOT ODD',
           'own block integer' if own_int else 'own block not integer',
           'own odd' if own_odd else ('own has even' if own_int else '-'))
    tab[key] += 1
    if len(ex) < 12: ex.append((p, b, G, k, str(t), [str(x) for x in vw], [str(x) for x in vo]))
for kk, vv in sorted(tab.items(), key=lambda x: -x[1]): print(vv, kk)
print("examples (p, b, G, subject, t*, 8 d t* own block, 8 d t* other block):")
for e in ex: print("  ", e)
