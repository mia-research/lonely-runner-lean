"""Owner: the cascade does not double, so extract how it avoids it.  Candidate law H2 (read off the chains): a runner d
sets a second time only if some runner setting in between has a zone at least as long as d's clear band, i.e.
1/(4e) >= 3/(4d), e <= d/3 (a runner at least 3 times slower bridges d's band on its own).  Exact.
Runs: the 1,350 Case C arrangements of case_c_map_v1 (seed 26), from the bound 1/(8 g_1).  Per repeat: the repeater, the
setters in between, whether one of them is >= 3x slower (H2), and the six's tightest five-spread sigma5/d_2."""
from fractions import Fraction as F
from math import floor
from itertools import combinations
from collections import Counter
from arrangement_lib import nd
import case_c_map_v1 as cm

def chain(ds, t):
    out = []
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return out, t
        cand = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
        d = max(cand, key=lambda x: cand[x]); out.append(d); t = cand[d]

def repeats(ch):
    """for each consecutive pair of settings of the same runner: (d, setters strictly between)"""
    last = {}; rep = []
    for i, d in enumerate(ch):
        if d in last: rep.append((d, ch[last[d] + 1:i]))
        last[d] = i
    return rep

if __name__ == '__main__':
    cm.rnd.seed(26)
    tot = nrep = h2 = 0; bad = []
    for shape in ('even', 'clumped+outliers', 'even+clump'):
        for g1div in (30, 100, 1000):
            n = 0
            while n < 150:
                g = cm.rest(shape); W6 = sum(g); g1 = max(1, W6 // (g1div - 1))
                if g1 + W6 <= 22 * g1: continue
                V = cm.arrangement([g1] + g)
                if len(set(V)) < 8: continue
                n += 1; tot += 1
                ds = sorted(v - V[0] for v in V[1:])
                ch, _ = chain(ds, F(1, 8 * g1))
                for d, mid in repeats(ch):
                    nrep += 1
                    ok = any(3 * e <= d for e in mid)
                    h2 += ok
                    if not ok:
                        six = ds[1:]; s5 = min(max(c) - min(c) for c in combinations(six, 5))
                        bad.append((shape, g1div, ds.index(d), [ds.index(e) for e in mid], float(F(s5, six[0])), g))
    print(f"Case C runs {tot}; repeated settings {nrep}; with a >= 3x slower setter in between (H2) {h2}; without {nrep - h2}")
    for b in bad[:40]:
        print(f"  H2 fails: {b[0]:17s} W/{b[1]:<5d} repeater rank {b[2]} (0 = g_1), between ranks {b[3]}, sigma5/d_2 {b[4]:.4f}, gaps g2..g7 {b[5]}")
    print("repeaters without a 3x-slower bridge, by sigma5/d_2 < 0.25:", Counter(b[4] < 0.25 for b in bad))
