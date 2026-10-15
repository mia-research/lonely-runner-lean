#!/usr/bin/env python3
"""E28: handovers at box deaths along grid-to-S deformations (paths as E21/E23: start v1*(1..5), move v5, v4, v3, v2
linearly; while one speed d_m moves, each lap box is alive on an exact closed interval of d_m; six_boxes_v1.py).
At every interior death of a box A (end of its interval in the direction of motion):
  - closing pair: the pair inequality of A that becomes tight there, (i entering at lap k_i, j leaving at lap k_j);
  - A's flank (runner whose entry is A's instant) and opening (its lap), laps, instant;
  - whether A held the isolation (A is the earliest alive box at the death point);
  - the takeover: boxes open on both sides of the death point; the earliest of them, with flank, opening, laps,
    instant, and the readings (fractional parts) of all runners at its instant.
Writes one TSV line per death of the isolation box; prints nothing else (summary by six_handover_read_v1.py).
Usage: six_handover_v1.py K out.tsv"""
import sys
from fractions import Fraction as F
s6 = F(1, 6)
src = open("six_boxes_v1.py").read().split("K = int(sys.argv[1])")[0]
ns = {}; exec(src, ns)
lonely_boxes, alive_interval, instant = ns["lonely_boxes"], ns["alive_interval"], ns["instant"]
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def earliest(V):
    t = F(1, 6 * min(V))
    for _ in range(100000):
        blk = [d for d in V if cd(d * t) < s6]
        if not blk: return t
        t = max((((d * t - s6).numerator // (d * t - s6).denominator) + 1 + s6) / d for d in blk)
def flank(V, k):
    t = instant(V, k); return [i + 1 for i in range(5) if (6*k[i]+1)/(6*V[i]) == t], t
def boxes_on_move(V, m, b):
    a = V[m]; lo_x, hi_x = min(a, b), max(a, b); boxes = {}
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
    for t in range(41): discover(lo_x + (hi_x - lo_x) * F(t, 40))
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
    return boxes, lo_x, hi_x, discover
K, out = int(sys.argv[1]), sys.argv[2]
sets = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]][::K]
chains = [tuple(map(int, l.split()[1:6])) for l in open("six_tau_over_v2.out")]
fo = open(out, "w")
fo.write("group\tset\tmover\tx\tA_laps\tA_flank\tA_instant\tclosing\tB_laps\tB_flank\tB_instant\tB_readings\tn_open\tcascade_agrees\n")
for group, sets_ in (("ordinary", sets), ("chain", chains)):
    for S in sets_:
        V = [F(S[0] * k) for k in range(1, 6)]
        for m in (4, 3, 2, 1):
            b = F(S[m])
            if V[m] == b: continue
            up = b > V[m]
            boxes, lo_x, hi_x, discover = boxes_on_move(V, m, b)
            for A, (l, h) in list(boxes.items()):
                x = h if up else l
                if not (lo_x < x < hi_x): continue
                W = list(V); W[m] = x
                alive_at = {k: instant(W, k) for k, (ll, hh) in boxes.items() if ll <= x <= hh}
                tA = alive_at[A]
                if tA != min(alive_at.values()): continue          # A did not hold the isolation
                discover(x + (F(1, 10**9) if up else -F(1, 10**9)))  # takeovers born at x
                alive_at = {k: instant(W, k) for k, (ll, hh) in boxes.items() if ll <= x <= hh}
                closing = [(i+1, j+1, A[i], A[j]) for i in range(5) for j in range(5)
                           if i != j and (6*A[i]+1)*W[j] == (6*A[j]+5)*W[i]]
                opn = {k: t for k, t in alive_at.items()
                       if (boxes[k][0] <= x < boxes[k][1] if up else boxes[k][0] < x <= boxes[k][1])}
                if not opn:
                    fo.write(f"{group}\t{S}\t{m+1}\t{x}\t{A}\t{flank(W, A)[0]}\t{tA}\t{closing}\tNONE\t\t\t\t0\n"); continue
                B = min(opn, key=lambda k: opn[k]); fB, tB = flank(W, B)
                Wp = list(V); Wp[m] = x + (F(1, 10**9) if up else -F(1, 10**9))
                ctrl = earliest(Wp) == instant(Wp, B)
                rd = tuple(str(w * tB - (w * tB).numerator // (w * tB).denominator) for w in W)
                fo.write(f"{group}\t{S}\t{m+1}\t{x}\t{A}\t{flank(W, A)[0]}\t{tA}\t{closing}\t{B}\t{fB}\t{tB}\t{rd}\t{len(opn)}\t{ctrl}\n")
            V[m] = b
fo.close()
