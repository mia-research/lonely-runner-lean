"""E150 v2: in the 772, does the slow group lead?  Cascade on S alone from t0 -> t_S; is the full landing t* = t_S (S's
own point, with G clear there)?  If not, is t* the first S-point with G clear, and how many S-points did G block?
The last is forced by definition when it holds (the cascade lands at the first all-clear instant); the content is
t* = t_S.  Exact."""
import pickle
from fractions import Fraction as F
from collections import Counter
from exceptions772_v1 import cascade_from, nd, E8
EX = pickle.load(open('exceptions772_v1.pkl', 'rb'))
C = Counter(); left = []
for kind, T, S, G, RG, Rs, bl in EX:
    t0 = F(1, 8 * T[0]); ts = cascade_from(T, t0); tS = cascade_from(S, t0)
    if ts == tS: C[(kind, "landing = S's own landing (G clear there)")] += 1
    else:
        C[(kind, "landing is neither G's nor S's own first point")] += 1; left.append((T, S, G, float(8 * T[0] * tS), float(8 * T[0] * ts)))
for k, v in sorted(C.items()): print("  %5d  %s" % (v, k))
print("left:", len(left))
for l in left[:20]: print("  ", l)
