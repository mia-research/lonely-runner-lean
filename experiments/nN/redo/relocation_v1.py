"""Does every arrangement only RELOCATE the isolation event?  Read through the cascade, in the manuscript's objects.

Every arrangement is an ideal AP plus deviations (Prop 2.2).  Arrangements are built that way: v_k = c + g*k + e_k,
k = 0..7, with deviations e_k drawn from [-rho*g, rho*g].  rho < 1/2 keeps the speed order; rho >= 1 lets runners lap
past other slots, which is the grid regime.  Also plain random arrangements.  Every speed positive, all distinct,
EVERY runner evaluated in its own signed differences delta_j = v_j - v_i.  Exact arithmetic.

For each runner the cascade is traced move by move (sec 6.1-6.2): at instant t the scale is D = 1/(8t), runner j sits at
sigma_j = 8*delta_j*t eighths = slot floor(sigma_j) + deviation in [0,1).  A runner is in the way iff sigma_j is within 1
of a multiple of 8 (band identity).  A move puts the setter exactly on 8N+1 eighths (slot 1, deviation 0).
At the fixed point t* (scale D* = 1/(8t*)) recorded:
  - the relocation factor t*/t_ref, t_ref = 1/(8*D_fit) the fitted AP's instant, D_fit = W/7 (sec 2.3);
  - moves, and which runner set each (nearest faster / nearest slower / other);
  - the slot pattern at t*: slots mod 8 of the seven others, whether it is a complete system {1..7}
    (the arrangement read as a grid at scale D*), how many share a slot;
  - that the flank sits exactly at 1/8 or 7/8 (Thm 6.2(d)) and every other position is in [1/8, 7/8]."""
import random, sys
from fractions import Fraction as F
from math import floor
from collections import Counter

def nd(x): x = x % 1; return min(x, 1 - x)

def trace(V, i, cap=200000):
    ds = [v - V[i] for j, v in enumerate(V) if j != i]
    m = min(abs(d) for d in ds)
    t = F(1, 8 * m); setters = []
    for _ in range(cap):
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t, setters, ds
        best = None
        for d in way:
            a = abs(d); K = floor(a * t - F(1, 8)) + 1
            o = (K + F(1, 8)) / a
            if best is None or o > best[0]: best = (o, d, K)
        t = best[0]; setters.append((best[1], best[2]))
    return None, setters, ds

def neighbour_kind(V, i, d):
    faster = sorted(v - V[i] for v in V if v > V[i]); slower = sorted((V[i] - v for v in V if v < V[i]))
    if d > 0 and faster and d == faster[0]: return 'nearest faster'
    if d < 0 and slower and -d == slower[0]: return 'nearest slower'
    return 'other'

def study(label, arrangements, out):
    tab = Counter(); reloc = []; moves = []; kinds = Counter(); share = Counter(); capped = 0
    for V in arrangements:
        W = max(V) - min(V); t_ref = F(7, 8 * W)
        for i in range(8):
            t, setters, ds = trace(V, i)
            if t is None: capped += 1; continue
            moves.append(len(setters)); reloc.append(t / t_ref)
            for d, K in setters: kinds[neighbour_kind(V, i, d)] += 1
            sig = [8 * d * t for d in ds]
            slots = [floor(s) % 8 for s in sig]
            on = sum(1 for s in sig if (s % 8) in (1, 7))
            assert all(F(1) <= s % 8 <= 7 for s in sig), (V, i)
            tab['flank exactly at 1/8 or 7/8'] += (on >= 1)
            tab['slot pattern complete {1..7}'] += (sorted(slots) == list(range(1, 8)))
            share[7 - len(set(slots))] += 1
            tab['runners'] += 1
            tab['event not moved (0 moves)'] += (len(setters) == 0)
    reloc.sort(); n = len(reloc)
    q = lambda p: float(reloc[min(n - 1, int(p * n))])
    print(f"\n== {label}: {len(arrangements)} arrangements, {tab['runners']} runners, capped {capped}", file=out)
    print(f"   fixed point reached: {tab['runners']} of {tab['runners'] + capped}", file=out)
    print(f"   event at the bound (0 moves): {tab['event not moved (0 moves)']};  moves max {max(moves)}, "
          f"mean {sum(moves)/len(moves):.2f}", file=out)
    print(f"   relocation factor t*/t_ref: min {q(0):.3f}  median {q(.5):.3f}  90% {q(.9):.3f}  max {float(reloc[-1]):.3f}", file=out)
    print(f"   flank exactly on 1/8 or 7/8: {tab['flank exactly at 1/8 or 7/8']};  every position in [1/8,7/8]: all (asserted)", file=out)
    print(f"   slot pattern at t* is a complete system {{1..7}} (a grid at scale D*): {tab['slot pattern complete {1..7}']}", file=out)
    print(f"   runners sharing a slot at t*, by number of repeats: {dict(sorted(share.items()))}", file=out)
    tot = sum(kinds.values())
    print(f"   move setters: " + ", ".join(f"{k} {v} ({100*v/tot:.0f}%)" for k, v in kinds.most_common()) if tot else "   no moves", file=out)

if __name__ == '__main__':
    rnd = random.Random(2609); g = 840; out = sys.stdout
    def ap_dev(rho, count):
        res = []
        while len(res) < count:
            e = [rnd.randint(-int(rho * g), int(rho * g)) for _ in range(8)]
            V = sorted(10 * g + g * k + e[k] for k in range(8))
            if len(set(V)) == 8 and min(V) > 0: res.append(V)
        return res
    for rho in (F(1, 100), F(1, 20), F(1, 8), F(1, 4), F(1, 2), F(1), F(2), F(4), F(16)):
        study(f"AP gap {g} plus deviations up to rho = {rho}", ap_dev(rho, 400), out)
    rand = []
    while len(rand) < 400:
        V = sorted(rnd.sample(range(1, 10**6), 8)); rand.append(V)
    study("random arrangements in [1, 10^6] (each is its fitted AP plus deviations)", rand, out)
