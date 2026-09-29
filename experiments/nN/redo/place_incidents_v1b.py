"""E174 follow-up: the misses of place_incidents_v1 against a place just BEFORE a rung.

The listed misses land on a reading's opening just below a ladder rung a/q (25/176 below 1/7, 25/152 below 1/6,
25/128 below 1/5).  Place statement tested, per miss, by exact equality with the cascade's landing t*:
  S2  there is a rung a/q (2 <= q <= 8, gcd(a, q) = 1, a/q >= t*) such that t* is the LATEST opening at or before the
      rung over all readings: t* = max_e (floor(e a/q - 1/8) + 1/8)/e.  (The mirror of a separation: coming back from the
      rung, every reading is past its last opening there.)
Also recorded for each miss: the nearest rung above t*, the host's residue e mod q, and whether the incident's closer
is a reading in the way at the rung (so the gap is bounded above by the rung's own obstruction).
"""
import math, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from math import gcd
from place_incidents_v1 import chunk, boundaries
from quantity_tests_v1 import cd, E8


def last_opening(e, s):
    return (math.floor(e * s - E8) + E8) / e


def analyse(row):
    T, ts, n, p, c1 = row
    rungs = sorted({F(a, q) for q in range(2, 9) for a in range(1, q) if gcd(a, q) == 1 and F(a, q) >= ts})
    s2 = None
    for r in rungs:
        lo = max(last_opening(e, r) for e in T)
        if lo == ts:
            s2 = r; break
    r0 = rungs[0] if rungs else None
    b = boundaries(T, ts)
    host = T[b['host']]; closer = T[b['closer']]
    closer_in_way_at_rung = (s2 is not None) and cd(closer * s2) < E8
    return dict(T=T, R=8 * T[0] * ts, s2=s2, r0=r0, q=(s2.denominator if s2 is not None else None),
                host=host, hostres=(host % s2.denominator if s2 is not None else None),
                closer_in_way=closer_in_way_at_rung, in_way_at_rung=(sorted(d for d in T if cd(d * s2) < E8) if s2 is not None else None))


def misses_of(first):
    return [analyse(r) for r in chunk(first) if r[3][0] == 'miss']


if __name__ == '__main__':
    with Pool(8) as pool:
        res = [x for part in pool.map(misses_of, range(1, 19)) for x in part]
    out = open('place_incidents_v1b.out', 'w'); out.write(__doc__ + "\n")
    hit = [x for x in res if x['s2'] is not None]
    out.write("misses: %d; S2 (latest opening at or before a rung a/q, q <= 8): %d\n" % (len(res), len(hit)))
    out.write("S2 by rung: %s\n" % dict(Counter(str(x['s2']) for x in hit).most_common()))
    out.write("S2 by q: %s\n" % dict(sorted(Counter(x['q'] for x in hit).items())))
    out.write("S2: the incident's closer is in the way at the rung: %d of %d\n" % (sum(x['closer_in_way'] for x in hit), len(hit)))
    out.write("S2: readings in the way at the rung (first 12): %s\n" % [(x['T'], str(x['s2']), x['in_way_at_rung']) for x in hit[:12]])
    lon = [x for x in hit if not x['in_way_at_rung']]
    out.write("S2 split: the rung itself is lonely (the incident's stretch contains the rung): %d; the rung is obstructed "
              "(the stretch ends before it): %d; obstructed <=> closer in the way at the rung: %s\n" %
              (len(lon), len(hit) - len(lon), all((not x['in_way_at_rung']) == (not x['closer_in_way']) for x in hit)))
    out.write("S2: host residue mod q: %s\n" % dict(Counter((x['q'], x['hostres']) for x in hit).most_common(20)))
    rest = [x for x in res if x['s2'] is None]
    out.write("\nnot S2: %d, listed (readings, R, nearest rung above):\n" % len(rest))
    for x in rest[:40]:
        out.write("   %s  R=%s  rung %s\n" % (x['T'], x['R'], x['r0']))
    out.close()
    print(open('place_incidents_v1b.out').read()[len(__doc__):])
