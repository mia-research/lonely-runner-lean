"""Recording the mirror per cell, and the induction as a length statement (scale-free).

(A) Every lonely cell [L, R] contains the mirror point of its boundary pair: a point of the lattice
    (1/Q)Z, Q = e_L + e_R (the cell theorem).  A cell shorter than 1/Q contains a point of a lattice
    of spacing 1/Q only by mechanism, not by size.  Per cell, over ALL lonely cells in [0, 1) of each
    hard set: the share shorter than 1/Q, and among those, how many contain a point of (1/Q)Z
    (should be all) against (1/(Q-1))Z and (1/(Q+1))Z (the control lattices).
(B) The induction without lattice or slack.  L6 = the lonely set of the six other disparities at
    1/8 (order seven gives it).  d_max is blocked on windows of length exactly 1/(4 d_max), one per
    lap, so a lonely cell of the six of length >= 1/(4 d_max) must meet a clear window of d_max.
    Per hard set: the longest lonely cell of the six, in units of 1/(4 d_max).
"""
import json, os, math
from fractions import Fraction as F
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
H = [tuple(S) for S in json.load(open(os.path.join(HERE, 'hard_sets_41_60.json')))]
E = F(1, 8)
def nd(x): x = x % 1; return min(x, 1 - x)
def cells(S):
    """Lonely cells in [0,1): maximal closed intervals where every ||d t|| >= 1/8, with their flanks."""
    pts = sorted({F(8 * N + s, 8 * d) % 1 for d in S for N in range(d + 1) for s in (1, -1)} | {F(0)})
    pts.append(F(1))
    out = []; cur = None
    for a, b in zip(pts, pts[1:]):
        mid = (a + b) / 2
        if all(nd(d * mid) >= E for d in S):
            if cur and cur[1] == a: cur[1] = b
            else:
                if cur: out.append(tuple(cur))
                cur = [a, b]
    if cur: out.append(tuple(cur))
    # one-point cells (an endpoint lonely but no open neighbourhood)
    for p in pts[:-1]:
        if all(nd(d * p) >= E for d in S) and not any(L <= p <= R for L, R in out): out.append((p, p))
    return out
def flank_at(S, t, side):
    for d in S:
        if (side == 'L' and (d * t) % 1 == E) or (side == 'R' and (d * t) % 1 == 1 - E): return d
    return None
def lattice_hit(L, R, Q):
    return math.ceil(L * Q) <= math.floor(R * Q)
A = Counter(); B = Counter(); worst = []
for S in H:
    for L, R in cells(S):
        eL, eR = flank_at(S, L, 'L'), flank_at(S, R, 'R')
        if eL is None or eR is None: continue
        Q = eL + eR
        A['cells'] += 1
        if R - L < F(1, Q):
            A['short'] += 1
            A['short, mirror lattice hit'] += lattice_hit(L, R, Q)
            A['short, Q-1 lattice hit'] += lattice_hit(L, R, Q - 1)
            A['short, Q+1 lattice hit'] += lattice_hit(L, R, Q + 1)
    six = [d for d in S if d != max(S)]
    longest = max((R - L for L, R in cells(six)), default=0)
    u = longest * 4 * max(S)
    B[('>= 1' if u >= 1 else '< 1')] += 1
    worst.append((float(u), S))
print("(A) per cell, hard sets:", dict(A))
worst.sort()
print("(B) longest lonely cell of the six, in units of 1/(4 d_max):", dict(B),
      "; smallest ratios:", [(round(u, 3), S) for u, S in worst[:5]], "; median", round(worst[len(worst) // 2][0], 2))
