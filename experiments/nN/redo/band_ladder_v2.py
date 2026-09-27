"""E151 v2: the regime generalised: the landing lies in a common block of the slow group S on some lap k (every slow
reading on lap k and clear: R in [(8k+1)/s_min(S) ... wait, per reading) -- tested directly: at the landing R*, are all
slow readings on one lap?  And is the landing the fast group's own point from the start of that block?  Band to 24 and
late fine shapes.  Exact."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from band_ladder_v1 import cascade_R, band, lateS, nd, E8
def G_from(G, R):
    t = R / 8
    while True:
        way = [d for d in G if nd(d * t) < E8]
        if not way: return 8 * t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
C = Counter()
for pop, sets in (('band24', band), ('late', lateS)):
    for s in sets:
        gi = max(range(1, 7), key=lambda i: s[i] / s[i - 1]); S = s[:gi]; G = s[gi:]
        R = cascade_R(s); lapsS = {floor(x * R / 8) for x in S}
        if len(lapsS) == 1:
            k = lapsS.pop(); start = F(8 * k + 1) / S[0]   # the slow group's common block on lap k starts at its slowest reading's exit
            own = G_from(G, start) == R
            C[(pop, '|S| = %d' % len(S), 'S on one lap (k = %d)' % min(k, 2), "landing = G's own point from the block start" if own else 'G delayed inside the block')] += 1
        else: C[(pop, '|S| = %d' % len(S), 'S split over laps')] += 1
for k, v in sorted(C.items()): print("  %6d  %s" % (v, k))
