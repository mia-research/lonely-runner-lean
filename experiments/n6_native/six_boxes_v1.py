#!/usr/bin/env python3
"""Step 2 (E23): lap boxes along grid-to-S paths, exact.
A lap box is a lap vector k (runner i reads in [k_i + 1/6, k_i + 5/6]); it is alive iff every ordered pair has
(6k_i+1) d_j <= (6k_j+5) d_i (GridStart_v1.lean, lap_box_lonely); its instant is max_i (6k_i+1)/(6d_i).
Paths as in six_deform_v1.py: start v1*(1..5), move v5, v4, v3, v2 linearly to S (v1 fixed, so d_min = v1 throughout).
While one speed d_m moves, each box is alive on an exact closed interval of d_m. We discover boxes until their
intervals cover the move, then list the DEGENERATE points: values of d_m inside no box's open interval. At each:
the boxes dying and born there, their tight pairs (i, j, k_i, k_j), their instants, and the displacement v1*(t_born - t_dying).
Usage: six_boxes_v1.py K   (every K-th residual set in [1,40] plus the 11 resonant chains)"""
import sys
from fractions import Fraction as F
from collections import Counter
s6 = F(1, 6)
def floor(x): return x.numerator // x.denominator
def lonely_boxes(V, W):
    ivs = [((F(0), W), ())]
    for v in V:
        new = []
        for (a, b), lab in ivs:
            k = max(floor(a * v - s6) - 1, 0)
            while True:
                l, r = (k + s6) / v, (k + 5 * s6) / v
                if l > b: break
                L, R = max(a, l), min(b, r)
                if L <= R: new.append(((L, R), lab + (k,)))
                k += 1
        ivs = new
    return {lab for _, lab in ivs}
def alive_interval(V, m, k):
    for i in range(5):
        for j in range(5):
            if i != m and j != m and (6*k[i]+1)*V[j] > (6*k[j]+5)*V[i]: return None
    lo = max((6*k[m]+1)*V[j]/(6*k[j]+5) for j in range(5) if j != m)
    hi = min((6*k[m]+5)*V[i]/(6*k[i]+1) for i in range(5) if i != m)
    return (lo, hi) if lo <= hi else None
def instant(V, k): return max((6*k[i]+1)/(6*V[i]) for i in range(5))
def tight(V, k):
    return [(i+1, j+1, k[i], k[j]) for i in range(5) for j in range(5) if i != j and (6*k[i]+1)*V[j] == (6*k[j]+5)*V[i]]
def move(V, m, b):
    a = V[m]; lo_x, hi_x = min(a, b), max(a, b)
    boxes = {}
    def discover(x):
        W = list(V); W[m] = x; Wd = F(3) / min(W)
        while True:
            found = lonely_boxes(W, Wd)
            if found: break
            Wd *= 2
        for k in found:
            if k not in boxes:
                iv = alive_interval(V, m, k)
                if iv: boxes[k] = iv
    for t in range(0, 41): discover(lo_x + (hi_x - lo_x) * F(t, 40))
    for _ in range(200):
        ivs = sorted((max(l, lo_x), min(h, hi_x)) for l, h in boxes.values() if h >= lo_x and l <= hi_x)
        reach = lo_x; gaps = []
        for l, h in ivs:
            if l > reach: gaps.append((reach, l))
            reach = max(reach, h)
        if reach < hi_x: gaps.append((reach, hi_x))
        if not gaps: break
        for g0, g1 in gaps:
            for x in (g0, (g0 + g1) / 2, g1): discover(x)
    else:
        raise RuntimeError("no cover")
    # degenerate points: endpoints in no open interval
    ends = sorted({e for l, h in boxes.values() for e in (l, h) if lo_x <= e <= hi_x} | {lo_x, hi_x})
    out = []
    for x in ends:
        if any(l < x < h for l, h in boxes.values()): continue
        W = list(V); W[m] = x
        alive = [k for k, (l, h) in boxes.items() if l <= x <= h]
        out.append((x, [(k, instant(W, k), tight(W, k), boxes[k]) for k in alive]))
    return out
K = int(sys.argv[1])
sets = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]][::K]
chains = [tuple(map(int, l.split()[1:6])) for l in open("six_tau_over_v2.out")]
for label, group in (("ordinary sample", sets), ("resonant chains", chains)):
    ndeg = Counter(); kinds = Counter(); disp = []; pair_types = Counter(); nalive = Counter(); examples = []
    for S in group:
        V = [F(S[0] * k) for k in range(1, 6)]
        for m in (4, 3, 2, 1):
            b = F(S[m]); a = V[m]
            if a == b: continue
            up = b > a
            for x, alive in move(V, m, b):
                if x == a and m == 4: continue        # the grid itself (step 1)
                if x == b: continue                  # endpoint of the move, not interior
                nalive[len(alive)] += 1
                dying = [z for z in alive if (z[3][1] == x if up else z[3][0] == x)]
                born = [z for z in alive if (z[3][0] == x if up else z[3][1] == x)]
                kinds[(len(dying), len(born))] += 1
                for z in alive:
                    for (i, j, ki, kj) in z[2]:
                        pair_types[(i, j)] += 1
                if dying and born:
                    d = max(z[1] for z in born) - min(z[1] for z in dying)
                    disp.append(S[0] * d)
                    if len(examples) < 6: examples.append((S, m+1, str(x), [(z[0], str(z[1]), z[2]) for z in alive]))
                ndeg[S] += 1
            V[m] = b
    print(f"== {label}: sets {len(group)}; interior degenerate points {sum(ndeg.values())}; sets with none {sum(1 for S in group if ndeg[S]==0)}")
    print("   boxes alive at a degenerate point:", dict(sorted(nalive.items())))
    print("   (dying, born) counts:", dict(sorted(kinds.items())))
    print("   tight pairs (entering runner i, leaving runner j):", dict(pair_types.most_common(12)))
    if disp:
        print(f"   displacement v1*(t_born - t_dying): min {float(min(disp)):.4f} max {float(max(disp)):.4f}; negative {sum(1 for d in disp if d<0)}, zero {sum(1 for d in disp if d==0)}")
    for e in examples: print("   e.g.", e)
