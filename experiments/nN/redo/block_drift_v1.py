"""WP3 item 2, steps 1-2 checked exactly.  For a top block and its longest blocked stretch: run the cascade through the
stretch; split the moves into the clear bands of the slowest runner d1 (band m = the moves whose landing lies in
[(m+1/8)/d1, (m+7/8)/d1]); for each band the relay word (runner, lap offset) and, for each link, its slack = 1/8 minus
the next runner's distance to its lap line at the landing (how deep inside the zone the landing falls).  Step 2 predicts:
the word repeats band to band with laps advanced by n_j = round(d_j/d1), and each link's slack changes by a constant
per band, set by the deviations eps_j = d_j/d1 - n_j (the deviation from the progression at scale d1).  Exact."""
from fractions import Fraction as F
from math import floor
from arrangement_lib import nd
from block_extremal_v1 import comps
def relay(B, a, b):
    t = a; moves = []
    while t < b:
        way = [d for d in B if nd(d * t) < F(1, 8)]
        if not way: break
        cand = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
        d = max(cand, key=lambda x: cand[x]); tn = cand[d]
        nxt = [e for e in B if nd(e * tn) < F(1, 8)]
        slack = {e: F(1, 8) - nd(e * tn) for e in nxt}
        moves.append((t, d, floor(d * tn), tn, slack)); t = tn
    return moves
for B in ([165, 166, 337, 494, 505, 772], [355, 357, 373, 524, 561, 784]):
    cs = comps(B); L, a, b = max(((q - p, p, q) for p, q in cs if p > 0)); d1 = min(B)
    eps = {d: F(d, d1) - round(F(d, d1)) for d in B}
    print(f"\n=== block {B}: stretch [{float(a):.5f}, {float(b):.5f}], deviations eps_j = d_j/d1 - n_j: "
          + ", ".join(f"{d}:{float(e):+.4f}" for d, e in eps.items()))
    mv = relay(B, a + F(1, 8 * d1), b)   # start at the centre of d1's first zone (the open stretch's endpoint is itself clear)
    bands = {}
    for (t, d, M, tn, slack) in mv:
        band = floor(tn * d1)
        bands.setdefault(band, []).append((d, M - round(F(d, d1) * band), slack))
    prev = None
    for band in sorted(bands):
        word = [(d, off) for d, off, s in bands[band]]
        same = prev is not None and word == prev
        links = "; ".join(f"{d}->" + ",".join(f"{e}:{float(s):.4f}" for e, s in sl.items()) for d, off, sl in bands[band])
        print(f"  d1-lap {band}: word {word}{'  (same word as previous band)' if same else ''}")
        print(f"      link slacks: {links}")
        prev = word
