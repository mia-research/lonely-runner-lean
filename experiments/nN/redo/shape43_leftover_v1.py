"""E393b (2026-10-05), shape43_leftover_v1: the leftover of the free-edge move on shape (4,3), through the cascade.
For a sample of the leftover sets (readings <= 48; every 8th leftover set of shape43_freeedge_v1): the exact cascade landing t*
of the whole set; its nearest class a/8 (a odd) and s = t* - a/8, direction d = sign(s); tau = 8|s| and which lonely window of the
cofactors E_1..E_4 contains tau (index counted from 0 in the cofactors' own lonely windows, tau-line, up to tau = 2).
Recorded: counts of (a, d), of the window index, of whether the landing is the exit of a multiple's cofactor zone or a non-multiple's.
Exact (Fractions).
"""
import itertools, math, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
import deform_pinch_v1 as D
from wave_incident_v1 import lonely_components
from shape43_freeedge_v1 import work as rule_work

def study(item):
    Ms, ns = item
    S = list(Ms) + list(ns)
    Es = [F(m // 8) for m in Ms]
    t = D.cascade_landing([F(x) for x in S], cap=100000)
    # nearest odd eighth
    k = round(t * 8)
    a = k if k % 2 else (k + 1 if (t * 8 - k) >= 0 else k - 1)
    s = t - F(a, 8)
    tau = 8 * abs(s)
    comps = lonely_components(Es, F(0), F(2))
    comps = [c for c in comps if c[0] > 0]
    idx = None
    for i, (lo, hi) in enumerate(comps):
        if lo <= tau <= hi:
            idx = i; break
    return (a % 8, 1 if s > 0 else (-1 if s < 0 else 0), idx, (Ms, ns))

if __name__ == '__main__':
    mults = list(range(8, 49, 8)); non = [c for c in range(1, 49) if c % 8]
    items = [(Ms, ns) for Ms in itertools.combinations(mults, 4) for ns in itertools.combinations(non, 3)]
    with Pool(4) as pool:
        res = []
        for i in range(0, len(items), 4000):
            res += pool.map(rule_work, [items[i:i + 500]] if False else [items[i:i + 4000]])
    left = [(r[0], r[1]) for c in res for r in c if not r[3]]
    samp = left[::8]
    with Pool(4) as pool:
        out_res = pool.map(study, samp, chunksize=50)
    o = open('shape43_leftover_v1.out', 'w'); o.write(__doc__ + "\n")
    o.write("leftover %d, sampled %d\n" % (len(left), len(samp)))
    o.write("(class a mod 8, direction): %s\n" % dict(Counter((r[0], r[1]) for r in out_res)))
    o.write("window index of tau among the cofactors' lonely windows: %s\n" % dict(sorted(Counter(r[2] for r in out_res).items(), key=lambda kv: (kv[0] is None, kv[0] or 0))))
    o.close(); print(open('shape43_leftover_v1.out').read()[len(__doc__):])
