"""Where the overlap at the mirror modulus comes from, and who drives the lattice cascade.

At Q = a + b (a < b the two largest) the instants are k/Q, 0 < k < Q; disparity d blocks k when
d*k mod Q lies within Q/8 of 0.  b reads as -a (the mirror), so six effective constraints.
mirror_union_v1: the union bound is 1.45 of the k, the true union 0.84.  Here, per hard set:

  pairs:   for each pair (d, d'), the overlap O = |B_d n B_d'| against independence
           E = |B_d||B_d'|/(Q-1), and the pair's link: d' = c*d + delta (mod Q) with |c| <= 4 and
           the least |delta| -- delta = 0 an exact link (B_d' is B_d read through x -> c x),
           |delta| small a near link (the two readings drift apart slowly in k).
  vertices: each d as p/q + delta/Q with q <= 8 (Theorem 5 at modulus q: vertex p/q, drift delta/Q
           per step of k).
  cascade: the deterministic cascade on the lattice, from the first k at which the smallest
           disparity clears: at k, the blocked runners each send k to their next clear k; take the
           largest; stop when none blocks.  Which runners drive it, how many moves.
"""
import json, os
from collections import Counter, defaultdict
from fractions import Fraction
from statistics import mean
HERE = os.path.dirname(os.path.abspath(__file__))
H = [tuple(S) for S in json.load(open(os.path.join(HERE, 'hard_sets_41_60.json')))]
H40 = [(1, 7, 10, 18, 24, 35, 37), (3, 5, 6, 7, 8, 26, 27), (3, 5, 6, 7, 8, 27, 30), (4, 5, 6, 8, 14, 27, 32),
       (5, 7, 8, 12, 26, 31, 36), (5, 8, 18, 28, 34, 38, 39)]

def blk(d, Q, k): x = d * k % Q; return not (Q <= 8 * x <= 7 * Q)

def link(d, e, Q):
    best = None
    for c in range(-4, 5):
        if c == 0: continue
        r = (e - c * d) % Q; r = min(r, Q - r)
        if best is None or r < best[1]: best = (c, r)
    return best

def vertex(d, Q):
    best = None
    for q in range(1, 9):
        p = round(d * q / Q); dl = d * q - p * Q      # d/Q = p/q + dl/(qQ)
        cand = (abs(dl) / q, q, p % q, dl)
        if best is None or cand < best: best = cand
    return best

def cascade(S, Q):
    eff = [d for d in S if d != max(S)]
    m = min(S); k = -(-Q // (8 * m)); moves = []; seen = set()
    while k < Q:
        bl = [d for d in eff if blk(d, Q, k)]
        if not bl: return k, moves
        nxt = {}
        for d in bl:
            j = k + 1
            while j < Q and blk(d, Q, j): j += 1
            nxt[d] = j
        dmax = max(bl, key=lambda d: nxt[d]); moves.append(dmax); k = nxt[dmax]
    return None, moves

def study(sets, label, show=0):
    share = Counter(); ex = defaultdict(float); tot_ex = 0.0; drivers = Counter(); nmoves = []
    vq = Counter()
    for S in sets:
        b, a = sorted(S)[-1], sorted(S)[-2]; Q = a + b
        eff = [d for d in S if d != b]
        B = {d: {k for k in range(1, Q) if blk(d, Q, k)} for d in eff}
        for i, d in enumerate(eff):
            for e in eff[i + 1:]:
                O = len(B[d] & B[e]); E = len(B[d]) * len(B[e]) / (Q - 1)
                c, r = link(d, e, Q)
                kind = 'exact' if r == 0 else ('near (|delta| <= Q/16)' if 16 * r <= Q else 'none')
                ex[kind] += (O - E) / (Q - 1); tot_ex += (O - E) / (Q - 1)
        for d in eff:
            vq[vertex(d, Q)[1]] += 1
        k, mv = cascade(S, Q)
        rank = {d: i for i, d in enumerate(sorted(S, reverse=True))}
        for d in mv: drivers[rank[d]] += 1
        nmoves.append(len(mv))
        if show:
            show -= 1
            print(f"  {S}  Q={Q}: vertices " + ", ".join(f"{d}~{vertex(d,Q)[2]}/{vertex(d,Q)[1]}{vertex(d,Q)[3]:+d}/{vertex(d,Q)[1]}Q" for d in eff)
                  + f"; cascade moves by {mv} -> k={k}")
    print(f"{label}: {len(sets)} sets")
    print(f"   overlap beyond independence (mean per set, in units of Q): total {tot_ex/len(sets):+.3f}; "
          + ", ".join(f"{k} {v/len(sets):+.3f}" for k, v in sorted(ex.items())))
    print(f"   nearest small-denominator vertex of each effective disparity, q: {sorted(vq.items())}")
    print(f"   cascade on the lattice: moves {Counter(nmoves).most_common(6)}; driver by rank "
          f"(0 = second largest a, 1 = third, ...): {sorted(drivers.items())}")

study(H40, "six hard sets of [1,40]", show=6)
study(H, "1,436 hard sets, largest 41..60")
