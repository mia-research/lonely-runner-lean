"""CERTIFIED check (exact rational interval arithmetic, branch and bound) of the non-synchronised step for
a fast level of 3 readings, over ALL starting phases:
  for every shape a = (1, r2, r3) with 10/9 <= r2, r3 >= (10/9) r2, r3 <= 9, and every phase
  phi in [0,1)^3, some s in [0, W], W = ROOM(3) = 27/20 turns, has ||phi_i + a_i s|| >= 1/8, i = 1..3.
A box of (r2, r3, phi1, phi2, phi3) is CERTIFIED by one s: at the box centre the shifted cascade gives
the first clear instant; s is the midpoint of that clear cell; then for each i the exact range of
phi_i + a_i s over the box must lie inside one band [m + 1/8, m + 7/8].  Otherwise the box is split on
the coordinate contributing most.  A centre whose first clear instant exceeds W is reported (it would
refute the step).  Every certified box is recorded; the union covers the whole domain."""
import time, sys
from fractions import Fraction as F
from math import floor, ceil
from full_phase_kappa_v1 import first_clear, ndist
W = F(27, 20)
def cell_mid(a, phi, s):
    ends = [(ceil(phi[i] + a[i] * s + F(1, 8)) - F(1, 8) - phi[i]) / a[i] for i in range(len(a))]
    e = min(ends); return (s + e) / 2
def certify(box):
    (r2lo, r2hi), (r3lo, r3hi), P = box[0], box[1], box[2:]
    c = [(lo + hi) / 2 for lo, hi in box]
    a = [F(1), c[0], c[1]]; phi = c[2:]
    if a[2] < a[1] * F(10, 9): a[2] = a[1] * F(10, 9)
    s0 = first_clear(a, phi)
    if s0 is None or s0 > W: return 'REFUTE', s0
    s = cell_mid(a, phi, s0)
    if s > W: s = s0
    rng = [((F(1), F(1)), P[0]), ((r2lo, r2hi), P[1]), ((r3lo, r3hi), P[2])]
    for (alo, ahi), (plo, phi_hi) in rng:
        lo = plo + alo * s; hi = phi_hi + ahi * s
        m = floor(lo - F(1, 8))
        if not (m + F(1, 8) <= lo and hi <= m + F(7, 8)): return 'SPLIT', None
    return 'OK', s
def split(box):
    widths = [(box[0][1] - box[0][0]) * W, (box[1][1] - box[1][0]) * W] + [hi - lo for lo, hi in box[2:]]
    k = max(range(5), key=lambda i: widths[i]); lo, hi = box[k]; mid = (lo + hi) / 2
    return [box[:k] + [(lo, mid)] + box[k + 1:], box[:k] + [(mid, hi)] + box[k + 1:]]
if __name__ == "__main__":
    t0 = time.time()
    # r2 in [10/9, 81/10], r3 in [r2*10/9, 9]: cover with r3 in [100/81, 9] and discard boxes entirely below r2*10/9
    stack = [[(F(10, 9), F(81, 10)), (F(100, 81), F(9)), (F(0), F(1)), (F(0), F(1)), (F(0), F(1))]]
    ok = split_n = 0; refute = []; vol = F(0)
    def V(b):
        v = F(1)
        for lo, hi in b: v *= hi - lo
        return v
    total = V(stack[0]); cap = int(sys.argv[1]) if len(sys.argv) > 1 else 3_000_000
    while stack and ok + split_n < cap:
        box = stack.pop()
        if box[1][1] < box[0][0] * F(10, 9): vol += V(box); continue   # outside the domain (r3 < (10/9) r2)
        verdict, s = certify(box)
        if verdict == 'OK': ok += 1; vol += V(box)
        elif verdict == 'REFUTE':
            refute.append((box, s)); 
            if len(refute) > 5: break
        else: split_n += 1; stack.extend(split(box))
        if (ok + split_n) % 200000 == 0: print(f"  ... certified {ok} ({float(vol / total):.4%} of the box volume incl. excluded region), split {split_n}, open {len(stack)}  ({time.time()-t0:.0f}s)", flush=True)
    print(f"f=3 over all shapes and phases: certified volume {float(vol / total):.4%} (incl. the excluded region r3 < 10 r2/9); certified boxes {ok}; splits {split_n}; open boxes left {len(stack)}; refutations {len(refute)}  ({time.time()-t0:.0f}s)")
    for box, s in refute[:3]: print(f"   REFUTING centre: box {[(float(lo), float(hi)) for lo, hi in box]}, first clear {s}")
    print("CERTIFIED" if not stack and not refute else "NOT COMPLETE")
